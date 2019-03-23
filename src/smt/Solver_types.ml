
module Vec = Msat.Vec
module Log = Msat.Log

module Fmt = CCFormat

(* for objects that are expanded on demand only *)
type 'a lazily_expanded =
  | Lazy_some of 'a
  | Lazy_none

(* main term cell. *)
type term = {
  mutable term_id: int; (* unique ID *)
  mutable term_ty: ty;
  term_view : term term_view;
}

(* term shallow structure *)
and 'a term_view =
  | Bool of bool
  | App_cst of cst * 'a IArray.t (* full, first-order application *)
  | Eq of 'a * 'a
  | If of 'a * 'a * 'a
  | Not of 'a

(* boolean literal *)
and lit = {
  lit_term: term;
  lit_sign: bool;
}

and cst = {
  cst_id: ID.t;
  cst_view: cst_view;
}

and cst_view =
  | Cst_undef of fun_ty (* simple undefined constant *)
  | Cst_def of {
      pp : 'a. ('a Fmt.printer -> 'a IArray.t Fmt.printer) option;
      abs : self:term -> term IArray.t -> term * bool; (* remove the sign? *)
      do_cc: bool; (* participate in congruence closure? *)
      relevant : 'a. ID.t -> 'a IArray.t -> int -> bool; (* relevant argument? *)
      ty : ID.t -> term IArray.t -> ty; (* compute type *)
      eval: value IArray.t -> value; (* evaluate term *)
    }
(** Methods on the custom term view whose arguments are ['a].
    Terms must be printable, and provide some additional theory handles.

    - [relevant] must return a subset of [args] (possibly the same set).
      The terms it returns will be activated and evaluated whenever possible.
      Terms in [args \ relevant args] are considered for
      congruence but not for evaluation.
*)

(** Function type *)
and fun_ty = {
  fun_ty_args: ty list;
  fun_ty_ret: ty;
}

(** Hashconsed type *)
and ty = {
  mutable ty_id: int;
  ty_view: ty_view;
}

and ty_view =
  | Ty_prop
  | Ty_atomic of {
      def: ty_def;
      args: ty list;
      card: ty_card lazy_t;
    }

and ty_def =
  | Ty_uninterpreted of ID.t
  | Ty_def of {
      id: ID.t;
      pp: ty Fmt.printer -> ty list Fmt.printer;
      default_val: value list -> value; (* default value of this type *)
      card: ty list -> ty_card;
    }

and ty_card =
  | Finite
  | Infinite

(** Semantic values, used for models (and possibly model-constructing calculi) *)
and value =
  | V_bool of bool
  | V_element of {
      id: ID.t;
      ty: ty;
    } (** a named constant, distinct from any other constant *)
  | V_custom of {
      view: value_custom_view;
      pp: value_custom_view Fmt.printer;
      eq: value_custom_view -> value_custom_view -> bool;
      hash: value_custom_view -> int;
    } (** Custom value *)

and value_custom_view = ..

type proof = Proof_default

type sat_actions = (Msat.void, lit, Msat.void, proof) Msat.acts

let[@inline] term_equal_ (a:term) b = a==b
let[@inline] term_hash_ a = a.term_id
let[@inline] term_cmp_ a b = CCInt.compare a.term_id b.term_id

let cmp_lit a b =
  let c = CCBool.compare a.lit_sign b.lit_sign in
  if c<>0 then c
  else term_cmp_ a.lit_term b.lit_term

let cst_compare a b = ID.compare a.cst_id b.cst_id

let hash_lit a =
  let sign = a.lit_sign in
  Hash.combine3 2 (Hash.bool sign) (term_hash_ a.lit_term)

let pp_cst out a = ID.pp out a.cst_id
let id_of_cst a = a.cst_id

let[@inline] eq_ty a b = a.ty_id = b.ty_id

let eq_value a b = match a, b with
  | V_bool a, V_bool b -> a=b
  | V_element e1, V_element e2 ->
    ID.equal e1.id e2.id && eq_ty e1.ty e2.ty
  | V_custom x1, V_custom x2 ->
    x1.eq x1.view x2.view
  | V_bool _, _ | V_element _, _ | V_custom _, _
    -> false

let hash_value a = match a with
  | V_bool a -> Hash.bool a
  | V_element e -> ID.hash e.id
  | V_custom x -> x.hash x.view

let pp_value out = function
  | V_bool b -> Fmt.bool out b
  | V_element e -> ID.pp out e.id
  | V_custom c -> c.pp out c.view

let pp_db out (i,_) = Format.fprintf out "%%%d" i

let rec pp_ty out t = match t.ty_view with
  | Ty_prop -> Fmt.string out "prop"
  | Ty_atomic {def=Ty_uninterpreted id; args=[]; _} -> ID.pp out id
  | Ty_atomic {def=Ty_uninterpreted id; args; _} ->
    Fmt.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list pp_ty) args
  | Ty_atomic {def=Ty_def def; args; _} -> def.pp pp_ty out args

let pp_term_view_gen ~pp_id ~pp_t out = function
  | Bool true -> Fmt.string out "true"
  | Bool false -> Fmt.string out "false"
  | App_cst ({cst_view=Cst_def {pp=Some pp_custom;_};_},l) -> pp_custom pp_t out l
  | App_cst (c, a) when IArray.is_empty a ->
    pp_id out (id_of_cst c)
  | App_cst (f,l) ->
    Fmt.fprintf out "(@[<1>%a@ %a@])" pp_id (id_of_cst f) (Util.pp_iarray pp_t) l
  | Eq (a,b) -> Fmt.fprintf out "(@[<hv>=@ %a@ %a@])" pp_t a pp_t b
  | If (a, b, c) ->
    Fmt.fprintf out "(@[if %a@ %a@ %a@])" pp_t a pp_t b pp_t c
  | Not u -> Fmt.fprintf out "(@[not@ %a@])" pp_t u

let pp_term_top ~ids out t =
  let rec pp out t =
    pp_rec out t;
    (* FIXME if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id; *)
  and pp_rec out t = pp_term_view_gen ~pp_id ~pp_t:pp_rec out t.term_view
  and pp_id = if ids then ID.pp else ID.pp_name in
  pp out t

let pp_term = pp_term_top ~ids:false
let pp_term_view = pp_term_view_gen ~pp_id:ID.pp_name ~pp_t:pp_term

let pp_lit out l =
  if l.lit_sign then pp_term out l.lit_term
  else Format.fprintf out "(@[@<1>¬@ %a@])" pp_term l.lit_term

let pp_proof out = function
  | Proof_default -> Fmt.fprintf out "<default proof>"
