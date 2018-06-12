
module Fmt = CCFormat
module Node_bits = CCBitField.Make(struct end)

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
  | If of 'a * 'a * 'a

(** A node of the congruence closure.
    An equivalence class is represented by its "root" element,
    the representative.

    If there is a normal form in the congruence class, then the
    representative is a normal form *)
and cc_node = {
  n_term: term;
  mutable n_bits: Node_bits.t; (* bitfield for various properties *)
  mutable n_parents: cc_node Bag.t; (* parent terms of the whole equiv class *)
  mutable n_root: cc_node; (* representative of congruence class (itself if a representative) *)
  mutable n_expl: explanation_forest_link; (* the rooted forest for explanations *)
  mutable n_payload: cc_node_payload list; (* list of theory payloads *)
  mutable n_tags: (cc_node * explanation) Util.Int_map.t; (* "distinct" tags (i.e. set of `(distinct t1…tn)` terms this belongs to *)
}

(** Theory-extensible payloads *)
and cc_node_payload = ..

and explanation_forest_link =
  | E_none
  | E_some of {
      next: cc_node;
      expl: explanation;
    }

(* atomic explanation in the congruence closure *)
and explanation =
  | E_reduction (* by pure reduction, tautologically equal *)
  | E_merges of (cc_node * cc_node) IArray.t (* caused by these merges *)
  | E_lit of lit (* because of this literal *)
  | E_lits of lit list (* because of this (true) conjunction *)

(* boolean literal *)
and lit = {
  lit_view: lit_view;
  lit_sign: bool;
}

and lit_view =
  | Lit_fresh of ID.t (* fresh literals *)
  | Lit_atom of term

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

let[@inline] term_equal_ (a:term) b = a==b
let[@inline] term_hash_ a = a.term_id
let[@inline] term_cmp_ a b = CCInt.compare a.term_id b.term_id

let cmp_lit a b =
  let c = CCBool.compare a.lit_sign b.lit_sign in
  if c<>0 then c
  else (
    let int_of_cell_ = function
      | Lit_fresh _ -> 0
      | Lit_atom _ -> 1
    in
    match a.lit_view, b.lit_view with
      | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
      | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
      | Lit_fresh _, _ | Lit_atom _, _
        -> CCInt.compare (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)
  )

let cst_compare a b = ID.compare a.cst_id b.cst_id

let hash_lit a =
  let sign = a.lit_sign in
  match a.lit_view with
    | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
    | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)

let cmp_cc_node a b = term_cmp_ a.n_term b.n_term

let rec cmp_exp a b =
  let toint = function
    | E_merges _ -> 0 | E_lit _ -> 1
    | E_reduction -> 2 | E_lits _ -> 3
  in
  begin match a, b with
    | E_merges l1, E_merges l2 ->
      IArray.compare (CCOrd.pair cmp_cc_node cmp_cc_node) l1 l2
    | E_reduction, E_reduction -> 0
    | E_lit l1, E_lit l2 -> cmp_lit l1 l2
    | E_lits l1, E_lits l2 -> CCList.compare cmp_lit l1 l2
    | E_merges _, _ | E_lit _, _ | E_lits _, _ | E_reduction, _
      -> CCInt.compare (toint a)(toint b)
  end

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

let pp_term_view ~pp_id ~pp_t out = function
  | Bool true -> Fmt.string out "true"
  | Bool false -> Fmt.string out "false"
  | App_cst ({cst_view=Cst_def {pp=Some pp_custom;_};_},l) -> pp_custom pp_t out l
  | App_cst (c, a) when IArray.is_empty a ->
    pp_id out (id_of_cst c)
  | App_cst (f,l) ->
    Fmt.fprintf out "(@[<1>%a@ %a@])" pp_id (id_of_cst f) (Util.pp_iarray pp_t) l
  | If (a, b, c) ->
    Fmt.fprintf out "(@[if %a@ %a@ %a@])" pp_t a pp_t b pp_t c

let pp_term_top ~ids out t =
  let rec pp out t =
    pp_rec out t;
    (* FIXME if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id; *)
  and pp_rec out t = pp_term_view ~pp_id ~pp_t:pp_rec out t.term_view
  and pp_id = if ids then ID.pp else ID.pp_name in
  pp out t

let pp_term = pp_term_top ~ids:false
let pp_term_view = pp_term_view ~pp_id:ID.pp_name ~pp_t:pp_term

let pp_lit out l =
  let pp_lit_view out = function
    | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
    | Lit_atom t -> pp_term out t
  in
  if l.lit_sign then pp_lit_view out l.lit_view
  else Format.fprintf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

let pp_cc_node out n = pp_term out n.n_term

let pp_explanation out (e:explanation) = match e with
  | E_reduction -> Fmt.string out "reduction"
  | E_lit lit -> pp_lit out lit
  | E_lits l -> CCFormat.Dump.list pp_lit out l
  | E_merges l ->
    Format.fprintf out "(@[<hv1>merges@ %a@])"
      Fmt.(seq ~sep:(return "@ ") @@ within "[" "]" @@ hvbox @@
        pair ~sep:(return "@ <-> ") pp_cc_node pp_cc_node)
      (IArray.to_seq l)
