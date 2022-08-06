(** Basic type definitions for Sidekick_base *)

(*

open Sidekick_core
module CC_view = Sidekick_cc.View
(* FIXME
   module Proof_ser = Sidekick_base_proof_trace.Proof_ser
   module Storage = Sidekick_base_proof_trace.Storage
*)

let hash_z = Z.hash
let[@inline] hash_q q = CCHash.combine2 (hash_z (Q.num q)) (hash_z (Q.den q))

module LRA_pred = struct
  type t = Sidekick_th_lra.Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  let to_string = function
    | Lt -> "<"
    | Leq -> "<="
    | Neq -> "!="
    | Eq -> "="
    | Gt -> ">"
    | Geq -> ">="

  let pp out p = Fmt.string out (to_string p)
end

module LRA_op = struct
  type t = Sidekick_th_lra.op = Plus | Minus

  let to_string = function
    | Plus -> "+"
    | Minus -> "-"

  let pp out p = Fmt.string out (to_string p)
end

module LRA_view = struct
  type 'a t =
    | Pred of LRA_pred.t * 'a * 'a
    | Op of LRA_op.t * 'a * 'a
    | Mult of Q.t * 'a
    | Const of Q.t
    | Var of 'a
    | To_real of 'a

  let map ~f_c f (l : _ t) : _ t =
    match l with
    | Pred (p, a, b) -> Pred (p, f a, f b)
    | Op (p, a, b) -> Op (p, f a, f b)
    | Mult (n, a) -> Mult (f_c n, f a)
    | Const c -> Const (f_c c)
    | Var x -> Var (f x)
    | To_real x -> To_real (f x)

  let iter f l : unit =
    match l with
    | Pred (_, a, b) | Op (_, a, b) ->
      f a;
      f b
    | Mult (_, x) | Var x | To_real x -> f x
    | Const _ -> ()

  let pp ~pp_t out = function
    | Pred (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_pred.to_string p) pp_t a pp_t b
    | Op (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_op.to_string p) pp_t a pp_t b
    | Mult (n, x) -> Fmt.fprintf out "(@[*@ %a@ %a@])" Q.pp_print n pp_t x
    | Const q -> Q.pp_print out q
    | Var x -> pp_t out x
    | To_real x -> Fmt.fprintf out "(@[to_real@ %a@])" pp_t x

  let hash ~sub_hash = function
    | Pred (p, a, b) -> Hash.combine4 81 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Op (p, a, b) -> Hash.combine4 82 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Mult (n, x) -> Hash.combine3 83 (hash_q n) (sub_hash x)
    | Const q -> Hash.combine2 84 (hash_q q)
    | Var x -> sub_hash x
    | To_real x -> Hash.combine2 85 (sub_hash x)

  let equal ~sub_eq l1 l2 =
    match l1, l2 with
    | Pred (p1, a1, b1), Pred (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Op (p1, a1, b1), Op (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Const a1, Const a2 -> Q.equal a1 a2
    | Mult (n1, x1), Mult (n2, x2) -> Q.equal n1 n2 && sub_eq x1 x2
    | Var x1, Var x2 | To_real x1, To_real x2 -> sub_eq x1 x2
    | (Pred _ | Op _ | Const _ | Mult _ | Var _ | To_real _), _ -> false
end

module LIA_pred = LRA_pred
module LIA_op = LRA_op

module LIA_view = struct
  type 'a t =
    | Pred of LIA_pred.t * 'a * 'a
    | Op of LIA_op.t * 'a * 'a
    | Mult of Z.t * 'a
    | Const of Z.t
    | Var of 'a

  let map ~f_c f (l : _ t) : _ t =
    match l with
    | Pred (p, a, b) -> Pred (p, f a, f b)
    | Op (p, a, b) -> Op (p, f a, f b)
    | Mult (n, a) -> Mult (f_c n, f a)
    | Const c -> Const (f_c c)
    | Var x -> Var (f x)

  let iter f l : unit =
    match l with
    | Pred (_, a, b) | Op (_, a, b) ->
      f a;
      f b
    | Mult (_, x) | Var x -> f x
    | Const _ -> ()

  let pp ~pp_t out = function
    | Pred (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_pred.to_string p) pp_t a pp_t b
    | Op (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_op.to_string p) pp_t a pp_t b
    | Mult (n, x) -> Fmt.fprintf out "(@[*@ %a@ %a@])" Z.pp_print n pp_t x
    | Const n -> Z.pp_print out n
    | Var x -> pp_t out x

  let hash ~sub_hash = function
    | Pred (p, a, b) -> Hash.combine4 81 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Op (p, a, b) -> Hash.combine4 82 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Mult (n, x) -> Hash.combine3 83 (hash_z n) (sub_hash x)
    | Const n -> Hash.combine2 84 (hash_z n)
    | Var x -> sub_hash x

  let equal ~sub_eq l1 l2 =
    match l1, l2 with
    | Pred (p1, a1, b1), Pred (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Op (p1, a1, b1), Op (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Const a1, Const a2 -> Z.equal a1 a2
    | Mult (n1, x1), Mult (n2, x2) -> Z.equal n1 n2 && sub_eq x1 x2
    | Var x1, Var x2 -> sub_eq x1 x2
    | (Pred _ | Op _ | Const _ | Mult _ | Var _), _ -> false

  (* convert the whole structure to reals *)
  let to_lra f l : _ LRA_view.t =
    match l with
    | Pred (p, a, b) -> LRA_view.Pred (p, f a, f b)
    | Op (op, a, b) -> LRA_view.Op (op, f a, f b)
    | Mult (c, x) -> LRA_view.Mult (Q.of_bigint c, f x)
    | Const x -> LRA_view.Const (Q.of_bigint x)
    | Var v -> LRA_view.Var (f v)
end

type term = Term.t
type ty = Term.t
type value = Term.t

type fun_view =
  | Fun_undef of ty (* simple undefined constant *)
  | Fun_select of select
  | Fun_cstor of cstor
  | Fun_is_a of cstor
  | Fun_def of {
      pp: 'a. ('a Fmt.printer -> 'a array Fmt.printer) option;
      abs: self:term -> term array -> term * bool; (* remove the sign? *)
      do_cc: bool; (* participate in congruence closure? *)
      relevant: 'a. ID.t -> 'a array -> int -> bool; (* relevant argument? *)
      ty: ID.t -> term array -> ty; (* compute type *)
      eval: value array -> value; (* evaluate term *)
    }
      (** Methods on the custom term view whose arguments are ['a].
    Terms must be printable, and provide some additional theory handles.

    - [relevant] must return a subset of [args] (possibly the same set).
      The terms it returns will be activated and evaluated whenever possible.
      Terms in [args \ relevant args] are considered for
      congruence but not for evaluation.
*)

and ty_view =
  | Ty_int
  | Ty_real
  | Ty_uninterpreted of ID.t
  | Ty_data of { data: data }
  | Ty_def of {
      id: ID.t;
      pp: ty Fmt.printer -> ty list Fmt.printer;
      default_val: value list -> value; (* default value of this type *)
    }

and data = {
  data_id: ID.t;
  data_cstors: cstor ID.Map.t lazy_t;
  data_as_ty: ty lazy_t;
}

and cstor = {
  cstor_id: ID.t;
  cstor_is_a: ID.t;
  mutable cstor_arity: int;
  cstor_args: select list lazy_t;
  cstor_ty_as_data: data;
  cstor_ty: ty lazy_t;
}

and select = {
  select_id: ID.t;
  select_cstor: cstor;
  select_ty: ty lazy_t;
  select_i: int;
}

(* FIXME: just use  terms; introduce a Const.view for V_element
   (** Semantic values, used for models (and possibly model-constructing calculi) *)
   type value_view =
     | V_element of { id: ID.t; ty: ty }
         (** a named constant, distinct from any other constant *)
     | V_cstor of { c: cstor; args: value list }
     | V_custom of {
         view: value_custom_view;
         pp: value_custom_view Fmt.printer;
         eq: value_custom_view -> value_custom_view -> bool;
         hash: value_custom_view -> int;
       }  (** Custom value *)
     | V_real of Q.t

   and value_custom_view = ..
*)

type definition = ID.t * ty * term

type statement =
  | Stmt_set_logic of string
  | Stmt_set_option of string list
  | Stmt_set_info of string * string
  | Stmt_data of data list
  | Stmt_ty_decl of ID.t * int (* new atomic cstor *)
  | Stmt_decl of ID.t * ty list * ty
  | Stmt_define of definition list
  | Stmt_assert of term
  | Stmt_assert_clause of term list
  | Stmt_check_sat of (bool * term) list
  | Stmt_get_model
  | Stmt_get_value of term list
  | Stmt_exit

type Const.view += Ty of ty_view

let ops_ty : Const.ops =
  (module struct
    let pp out = function
      | Ty ty ->
        (match ty with
        | Ty_real -> Fmt.string out "Real"
        | Ty_int -> Fmt.string out "Int"
        | Ty_atomic { def = Ty_uninterpreted id; args = []; _ } -> ID.pp out id
        | Ty_atomic { def = Ty_uninterpreted id; args; _ } ->
          Fmt.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list pp_ty) args
        | Ty_atomic { def = Ty_def def; args; _ } -> def.pp pp_ty out args
        | Ty_atomic { def = Ty_data d; args = []; _ } ->
          ID.pp out d.data.data_id
        | Ty_atomic { def = Ty_data d; args; _ } ->
          Fmt.fprintf out "(@[%a@ %a@])" ID.pp d.data.data_id
            (Util.pp_list pp_ty) args)
      | _ -> ()

    let equal a b =
      match a, b with
      | Ty a, Ty b ->
        (match a, b with
        | Ty_bool, Ty_bool | Ty_int, Ty_int | Ty_real, Ty_real -> true
        | Ty_atomic a1, Ty_atomic a2 ->
          equal_def a1.def a2.def && CCList.equal equal a1.args a2.args
        | (Ty_bool | Ty_atomic _ | Ty_real | Ty_int), _ -> false)
      | _ -> false

    let hash t =
      match t.ty_view with
      | Ty_bool -> Hash.int 1
      | Ty_real -> Hash.int 2
      | Ty_int -> Hash.int 3
      | Ty_atomic { def = Ty_uninterpreted id; args; _ } ->
        Hash.combine3 10 (ID.hash id) (Hash.list hash args)
      | Ty_atomic { def = Ty_def d; args; _ } ->
        Hash.combine3 20 (ID.hash d.id) (Hash.list hash args)
      | Ty_atomic { def = Ty_data d; args; _ } ->
        Hash.combine3 30 (ID.hash d.data.data_id) (Hash.list hash args)
  end)

(*
let rec eq_value a b =
  match a, b with
  | V_bool a, V_bool b -> a = b
  | V_element e1, V_element e2 -> ID.equal e1.id e2.id && eq_ty e1.ty e2.ty
  | V_custom x1, V_custom x2 -> x1.eq x1.view x2.view
  | V_cstor x1, V_cstor x2 ->
    eq_cstor x1.c x2.c && CCList.equal eq_value x1.args x2.args
  | V_real a, V_real b -> Q.equal a b
  | (V_bool _ | V_element _ | V_custom _ | V_cstor _ | V_real _), _ -> false

let rec hash_value a =
  match a with
  | V_bool a -> Hash.bool a
  | V_element e -> ID.hash e.id
  | V_custom x -> x.hash x.view
  | V_cstor x ->
    Hash.combine3 42 (ID.hash x.c.cstor_id) (Hash.list hash_value x.args)
  | V_real x -> Hash.combine3 50 (Z.hash @@ Q.num x) (Z.hash @@ Q.den x)

let rec pp_value out = function
  | V_bool b -> Fmt.bool out b
  | V_element e -> ID.pp out e.id
  | V_custom c -> c.pp out c.view
  | V_cstor { c; args = [] } -> ID.pp out c.cstor_id
  | V_cstor { c; args } ->
    Fmt.fprintf out "(@[%a@ %a@])" ID.pp c.cstor_id (Util.pp_list pp_value) args
  | V_real x -> Q.pp_print out x
  *)

let pp_term_view_gen ~pp_id ~pp_t out = function
  | Bool true -> Fmt.string out "true"
  | Bool false -> Fmt.string out "false"
  | App_fun ({ fun_view = Fun_def { pp = Some pp_custom; _ }; _ }, l) ->
    pp_custom pp_t out l
  | App_fun (c, [||]) -> pp_id out (id_of_fun c)
  | App_fun (f, l) ->
    Fmt.fprintf out "(@[<1>%a@ %a@])" pp_id (id_of_fun f) (Util.pp_array pp_t) l
  | Eq (a, b) -> Fmt.fprintf out "(@[<hv>=@ %a@ %a@])" pp_t a pp_t b
  | Not u -> Fmt.fprintf out "(@[not@ %a@])" pp_t u
  | Ite (a, b, c) ->
    Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" pp_t a pp_t b pp_t c
  | LRA l -> LRA_view.pp ~pp_t out l
  | LIA l ->
    LIA_view.pp ~pp_t out l;
    Fmt.string out "/ℤ"

let pp_term_top ~ids out t =
  let rec pp out t = pp_rec out t
  (* FIXME Fmt.fprintf out "/%d" t.term_id; *)
  and pp_rec out t = pp_term_view_gen ~pp_id ~pp_t:pp_rec out t.term_view
  and pp_id =
    if ids then
      ID.pp
    else
      ID.pp_name
  in
  pp out t

let pp_term = pp_term_top ~ids:false
let pp_term_view = pp_term_view_gen ~pp_id:ID.pp_name ~pp_t:pp_term

(** Types *)
module Ty : sig
  type t = ty
  type store = unit

  type view = ty_view =
    | Ty_bool
    | Ty_real
    | Ty_int
    | Ty_atomic of { def: ty_def; args: ty list; mutable finite: bool }

  type def = ty_def =
    | Ty_uninterpreted of ID.t
    | Ty_data of { data: data }
    | Ty_def of {
        id: ID.t;
        pp: ty Fmt.printer -> ty list Fmt.printer;
        default_val: value list -> value; (* default value of this type *)
      }

  val id : t -> int
  val view : t -> view
  val bool : store -> t
  val real : store -> t
  val int : store -> t
  val atomic : def -> t list -> t
  val id_of_def : def -> ID.t
  val atomic_uninterpreted : ID.t -> t
  val finite : t -> bool
  val set_finite : t -> bool -> unit
  val is_bool : t -> bool
  val is_uninterpreted : t -> bool
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer

  module Tbl : CCHashtbl.S with type key = t

  module Fun : sig
    type t = fun_ty

    val args : t -> ty list
    val ret : t -> ty
    val arity : t -> int
    val unfold : t -> ty list * ty
    val mk : ty list -> ty -> t
    val pp : t CCFormat.printer
  end
end = struct
  type t = ty
  type store = unit

  type view = ty_view =
    | Ty_bool
    | Ty_real
    | Ty_int
    | Ty_atomic of { def: ty_def; args: ty list; mutable finite: bool }

  type def = ty_def =
    | Ty_uninterpreted of ID.t
    | Ty_data of { data: data }
    | Ty_def of {
        id: ID.t;
        pp: ty Fmt.printer -> ty list Fmt.printer;
        default_val: value list -> value; (* default value of this type *)
      }

  let[@inline] id t = t.ty_id
  let[@inline] view t = t.ty_view
  let equal = eq_ty
  let[@inline] compare a b = CCInt.compare a.ty_id b.ty_id
  let[@inline] hash a = a.ty_id

  let equal_def d1 d2 =
    match d1, d2 with
    | Ty_uninterpreted id1, Ty_uninterpreted id2 -> ID.equal id1 id2
    | Ty_def d1, Ty_def d2 -> ID.equal d1.id d2.id
    | Ty_data d1, Ty_data d2 -> ID.equal d1.data.data_id d2.data.data_id
    | (Ty_uninterpreted _ | Ty_def _ | Ty_data _), _ -> false

  module H = Hashcons.Make (struct
    type t = ty

    let equal a b =
      match a.ty_view, b.ty_view with
      | Ty_bool, Ty_bool | Ty_int, Ty_int | Ty_real, Ty_real -> true
      | Ty_atomic a1, Ty_atomic a2 ->
        equal_def a1.def a2.def && CCList.equal equal a1.args a2.args
      | (Ty_bool | Ty_atomic _ | Ty_real | Ty_int), _ -> false

    let hash t =
      match t.ty_view with
      | Ty_bool -> Hash.int 1
      | Ty_real -> Hash.int 2
      | Ty_int -> Hash.int 3
      | Ty_atomic { def = Ty_uninterpreted id; args; _ } ->
        Hash.combine3 10 (ID.hash id) (Hash.list hash args)
      | Ty_atomic { def = Ty_def d; args; _ } ->
        Hash.combine3 20 (ID.hash d.id) (Hash.list hash args)
      | Ty_atomic { def = Ty_data d; args; _ } ->
        Hash.combine3 30 (ID.hash d.data.data_id) (Hash.list hash args)

    let set_id ty id =
      assert (ty.ty_id < 0);
      ty.ty_id <- id
  end)

  (* build a type *)
  let make_ : ty_view -> t =
    let tbl : H.t = H.create ~size:128 () in
    fun [@inline] c ->
      let ty = { ty_id = -1; ty_view = c } in
      H.hashcons tbl ty

  let finite t =
    match view t with
    | Ty_bool -> true
    | Ty_real | Ty_int -> false
    | Ty_atomic { finite = f; _ } -> f

  let set_finite t b =
    match view t with
    | Ty_bool | Ty_real | Ty_int -> assert false
    | Ty_atomic r -> r.finite <- b

  let bool () = make_ Ty_bool
  let real () = make_ Ty_real
  let int () = make_ Ty_int
  let atomic def args : t = make_ (Ty_atomic { def; args; finite = true })
  let atomic_uninterpreted id = atomic (Ty_uninterpreted id) []

  let id_of_def = function
    | Ty_uninterpreted id -> id
    | Ty_def { id; _ } -> id
    | Ty_data { data } -> data.data_id

  let is_bool t =
    match t.ty_view with
    | Ty_bool -> true
    | _ -> false

  let is_uninterpreted t =
    match t.ty_view with
    | Ty_atomic { def = Ty_uninterpreted _; _ } -> true
    | _ -> false

  let pp = pp_ty

  module Tbl = CCHashtbl.Make (struct
    type t = ty

    let equal = equal
    let hash = hash
  end)

  module Fun = struct
    type t = fun_ty

    let[@inline] args f = f.fun_ty_args
    let[@inline] ret f = f.fun_ty_ret
    let[@inline] arity f = List.length @@ args f
    let[@inline] mk args ret : t = { fun_ty_args = args; fun_ty_ret = ret }
    let[@inline] unfold t = args t, ret t

    let pp out f : unit =
      match args f with
      | [] -> pp out (ret f)
      | args ->
        Format.fprintf out "(@[(@[%a@])@ %a@])" (Util.pp_list pp) args pp
          (ret f)
  end
end

(** Function symbols *)
module Fun : sig
  (** Possible definitions for a function symbol *)
  type view = fun_view =
    | Fun_undef of fun_ty (* simple undefined constant *)
    | Fun_select of select
    | Fun_cstor of cstor
    | Fun_is_a of cstor
    | Fun_def of {
        pp: 'a. ('a Fmt.printer -> 'a array Fmt.printer) option;
        abs: self:term -> term array -> term * bool; (* remove the sign? *)
        do_cc: bool; (* participate in congruence closure? *)
        relevant: 'a. ID.t -> 'a array -> int -> bool;
        (* relevant argument? *)
        ty: ID.t -> term array -> ty; (* compute type *)
        eval: value array -> value; (* evaluate term *)
      }
        (** user defined function symbol.
            A good example can be found in {!Form} for boolean connectives. *)

  type t = fun_ = { fun_id: ID.t; fun_view: fun_view }
  (** A function symbol *)

  val id : t -> ID.t
  val view : t -> view
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val as_undefined : t -> (t * Ty.Fun.t) option
  val as_undefined_exn : t -> t * Ty.Fun.t
  val is_undefined : t -> bool
  val select : select -> t
  val select_idx : cstor -> int -> t
  val cstor : cstor -> t
  val is_a : cstor -> t
  val do_cc : t -> bool

  val mk_undef : ID.t -> Ty.Fun.t -> t
  (** Make a new uninterpreted function. *)

  val mk_undef' : ID.t -> Ty.t list -> Ty.t -> t

  val mk_undef_const : ID.t -> Ty.t -> t
  (** Make a new uninterpreted constant. *)

  val pp : t CCFormat.printer

  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end = struct
  type view = fun_view =
    | Fun_undef of fun_ty (* simple undefined constant *)
    | Fun_select of select
    | Fun_cstor of cstor
    | Fun_is_a of cstor
    | Fun_def of {
        pp: 'a. ('a Fmt.printer -> 'a array Fmt.printer) option;
        abs: self:term -> term array -> term * bool; (* remove the sign? *)
        do_cc: bool; (* participate in congruence closure? *)
        relevant: 'a. ID.t -> 'a array -> int -> bool;
        (* relevant argument? *)
        ty: ID.t -> term array -> ty; (* compute type *)
        eval: value array -> value; (* evaluate term *)
      }

  type t = fun_ = { fun_id: ID.t; fun_view: fun_view }

  let[@inline] id t = t.fun_id
  let[@inline] view t = t.fun_view
  let[@inline] make fun_id fun_view = { fun_id; fun_view }

  let as_undefined (c : t) =
    match view c with
    | Fun_undef ty -> Some (c, ty)
    | Fun_def _ | Fun_cstor _ | Fun_select _ | Fun_is_a _ -> None

  let[@inline] is_undefined c =
    match view c with
    | Fun_undef _ -> true
    | _ -> false

  let as_undefined_exn (c : t) =
    match as_undefined c with
    | Some tup -> tup
    | None -> assert false

  let[@inline] mk_undef id ty = make id (Fun_undef ty)
  let[@inline] mk_undef_const id ty = mk_undef id (Ty.Fun.mk [] ty)

  let[@inline] mk_undef' id args ret =
    mk_undef id { fun_ty_args = args; fun_ty_ret = ret }

  let is_a c : t = make c.cstor_is_a (Fun_is_a c)
  let cstor c : t = make c.cstor_id (Fun_cstor c)
  let select sel : t = make sel.select_id (Fun_select sel)

  let select_idx c i : t =
    let (lazy l) = c.cstor_args in
    match List.nth l i with
    | sel -> select sel
    | exception Not_found ->
      Error.errorf "invalid selector %d for cstor %a" i ID.pp c.cstor_id

  let[@inline] do_cc (c : t) : bool =
    match view c with
    | Fun_cstor _ | Fun_select _ | Fun_undef _ | Fun_is_a _ -> true
    | Fun_def { do_cc; _ } -> do_cc

  let equal a b = ID.equal a.fun_id b.fun_id
  let compare a b = ID.compare a.fun_id b.fun_id
  let hash t = ID.hash t.fun_id
  let pp out a = ID.pp out a.fun_id

  module As_key = struct
    type nonrec t = t

    let compare = compare
    let equal = equal
    let hash = hash
  end

  module Map = CCMap.Make (As_key)
  module Tbl = CCHashtbl.Make (As_key)
end

module Term_cell : sig
  type 'a view = 'a term_view =
    | Bool of bool
    | App_fun of fun_ * 'a array
    | Eq of 'a * 'a
    | Not of 'a
    | Ite of 'a * 'a * 'a
    | LRA of 'a LRA_view.t
    | LIA of 'a LIA_view.t

  type t = term view

  val equal : t -> t -> bool
  val hash : t -> int
  val true_ : t
  val false_ : t
  val const : fun_ -> t
  val app_fun : fun_ -> term array -> t
  val eq : term -> term -> t
  val not_ : term -> t
  val ite : term -> term -> term -> t
  val lra : term LRA_view.t -> t
  val lia : term LIA_view.t -> t

  val ty : t -> Ty.t
  (** Compute the type of this term cell. Not totally free *)

  val pp : t Fmt.printer
  val map : ('a -> 'b) -> 'a view -> 'b view
  val iter : ('a -> unit) -> 'a view -> unit

  module type ARG = sig
    type t

    val hash : t -> int
    val equal : t -> t -> bool
    val pp : t Fmt.printer
  end

  module Make_eq (X : ARG) : sig
    val equal : X.t view -> X.t view -> bool
    val hash : X.t view -> int
    val pp : X.t view Fmt.printer
  end
end = struct
  type 'a view = 'a term_view =
    | Bool of bool
    | App_fun of fun_ * 'a array
    | Eq of 'a * 'a
    | Not of 'a
    | Ite of 'a * 'a * 'a
    | LRA of 'a LRA_view.t
    | LIA of 'a LIA_view.t

  type t = term view

  module type ARG = sig
    type t

    val hash : t -> int
    val equal : t -> t -> bool
    val pp : t Fmt.printer
  end

  module Make_eq (A : ARG) = struct
    let sub_hash = A.hash
    let sub_eq = A.equal

    let hash (t : A.t view) : int =
      match t with
      | Bool b -> Hash.bool b
      | App_fun (f, l) -> Hash.combine3 4 (Fun.hash f) (Hash.iarray sub_hash l)
      | Eq (a, b) -> Hash.combine3 12 (sub_hash a) (sub_hash b)
      | Not u -> Hash.combine2 70 (sub_hash u)
      | Ite (a, b, c) -> Hash.combine4 80 (sub_hash a) (sub_hash b) (sub_hash c)
      | LRA l -> LRA_view.hash ~sub_hash l
      | LIA l -> LIA_view.hash ~sub_hash l

    (* equality that relies on physical equality of subterms *)
    let equal (a : A.t view) b : bool =
      match a, b with
      | Bool b1, Bool b2 -> CCBool.equal b1 b2
      | App_fun (f1, a1), App_fun (f2, a2) ->
        Fun.equal f1 f2 && CCArray.equal sub_eq a1 a2
      | Eq (a1, b1), Eq (a2, b2) -> sub_eq a1 a2 && sub_eq b1 b2
      | Not a, Not b -> sub_eq a b
      | Ite (a1, b1, c1), Ite (a2, b2, c2) ->
        sub_eq a1 a2 && sub_eq b1 b2 && sub_eq c1 c2
      | LRA l1, LRA l2 -> LRA_view.equal ~sub_eq l1 l2
      | LIA l1, LIA l2 -> LIA_view.equal ~sub_eq l1 l2
      | (Bool _ | App_fun _ | Eq _ | Not _ | Ite _ | LRA _ | LIA _), _ -> false

    let pp = pp_term_view_gen ~pp_id:ID.pp_name ~pp_t:A.pp
  end
  [@@inline]

  include Make_eq (struct
    type t = term

    let equal (t1 : t) t2 = t1 == t2
    let hash (t : term) : int = CCHash.int t.term_id
    let pp = pp_term
  end)

  let true_ = Bool true
  let false_ = Bool false
  let app_fun f a = App_fun (f, a)
  let const c = App_fun (c, CCArray.empty)

  let eq a b =
    if term_equal_ a b then
      Bool true
    else (
      (* canonize *)
      let a, b =
        if a.term_id > b.term_id then
          b, a
        else
          a, b
      in
      Eq (a, b)
    )

  let not_ t =
    match t.term_view with
    | Bool b -> Bool (not b)
    | Not u -> u.term_view
    | _ -> Not t

  let[@inline] ite a b c = Ite (a, b, c)
  let[@inline] lra l : t = LRA l
  let[@inline] lia l : t = LIA l

  let ty (t : t) : Ty.t =
    match t with
    | Bool _ | Eq _ | Not _ -> Ty.bool ()
    | Ite (_, b, _) -> b.term_ty
    | App_fun (f, args) ->
      (match Fun.view f with
      | Fun_undef fty ->
        let ty_args, ty_ret = Ty.Fun.unfold fty in
        (* check arity *)
        if List.length ty_args <> CCArray.length args then
          Error.errorf "Term_cell.apply: expected %d args, got %d@ in %a"
            (List.length ty_args) (CCArray.length args) pp t;
        (* check types *)
        List.iteri
          (fun i ty_a ->
            let a = CCArray.get args i in
            if not @@ Ty.equal a.term_ty ty_a then
              Error.errorf
                "Term_cell.apply: %d-th argument mismatch:@ %a does not have \
                 type %a@ in %a"
                i pp_term a Ty.pp ty_a pp t)
          ty_args;
        ty_ret
      | Fun_is_a _ -> Ty.bool ()
      | Fun_def def -> def.ty f.fun_id args
      | Fun_select s -> Lazy.force s.select_ty
      | Fun_cstor c -> Lazy.force c.cstor_ty)
    | LRA l ->
      LRA_view.(
        (match l with
        | Pred _ -> Ty.bool ()
        | Op _ | Const _ | Mult _ | To_real _ -> Ty.real ()
        | Var x -> x.term_ty))
    | LIA l ->
      LIA_view.(
        (match l with
        | Pred _ -> Ty.bool ()
        | Op _ | Const _ | Mult _ -> Ty.int ()
        | Var x -> x.term_ty))

  let iter f view =
    match view with
    | Bool _ -> ()
    | App_fun (_, a) -> CCArray.iter f a
    | Not u -> f u
    | Eq (a, b) ->
      f a;
      f b
    | Ite (a, b, c) ->
      f a;
      f b;
      f c
    | LRA l -> LRA_view.iter f l
    | LIA l -> LIA_view.iter f l

  let map f view =
    match view with
    | Bool b -> Bool b
    | App_fun (fu, a) -> App_fun (fu, CCArray.map f a)
    | Not u -> Not (f u)
    | Eq (a, b) -> Eq (f a, f b)
    | Ite (a, b, c) -> Ite (f a, f b, f c)
    | LRA l -> LRA (LRA_view.map ~f_c:CCFun.id f l)
    | LIA l -> LIA (LIA_view.map ~f_c:CCFun.id f l)
end

(** Term creation and manipulation *)
module Term : sig
  type t = term = {
    mutable term_id: int;
    mutable term_ty: ty;
    term_view: t term_view;
  }

  type 'a view = 'a term_view =
    | Bool of bool
    | App_fun of fun_ * 'a array
    | Eq of 'a * 'a
    | Not of 'a
    | Ite of 'a * 'a * 'a
    | LRA of 'a LRA_view.t
    | LIA of 'a LIA_view.t

  val id : t -> int
  val view : t -> term view
  val ty : t -> Ty.t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int

  type store

  val create : ?size:int -> unit -> store
  val make : store -> t view -> t
  val true_ : store -> t
  val false_ : store -> t
  val bool : store -> bool -> t
  val const : store -> fun_ -> t
  val app_fun : store -> fun_ -> t array -> t
  val app_fun_l : store -> fun_ -> t list -> t
  val eq : store -> t -> t -> t
  val not_ : store -> t -> t
  val ite : store -> t -> t -> t -> t

  val app_undefined : store -> ID.t -> Ty.Fun.t -> t array -> t
  (** [app_undefined store f ty args] is [app store (Fun.mk_undef f ty) args].
      It builds a function symbol and applies it into a term immediately *)

  val const_undefined : store -> ID.t -> Ty.t -> t
  (** [const_undefined store f ty] is [const store (Fun.mk_undef_const f ty)].
      It builds a constant function symbol and makes it into a term
      immediately. *)

  val select : store -> select -> t -> t
  val app_cstor : store -> cstor -> t array -> t
  val is_a : store -> cstor -> t -> t
  val lra : store -> t LRA_view.t -> t
  val lia : store -> t LIA_view.t -> t

  module type ARITH_HELPER = sig
    type num

    val plus : store -> t -> t -> t
    val minus : store -> t -> t -> t
    val mult : store -> num -> t -> t
    val const : store -> num -> t
    val leq : store -> t -> t -> t
    val lt : store -> t -> t -> t
    val geq : store -> t -> t -> t
    val gt : store -> t -> t -> t
    val eq : store -> t -> t -> t
    val neq : store -> t -> t -> t
  end

  module LRA : ARITH_HELPER with type num := Q.t
  module LIA : ARITH_HELPER with type num := Z.t

  val abs : store -> t -> t * bool
  (** Obtain unsigned version of [t], + the sign as a boolean *)

  module Iter_dag : sig
    type t
    type order = Pre | Post

    val create : unit -> t
    val iter_dag : ?order:order -> t -> term -> term Iter.t
  end

  val iter_dag_with : order:Iter_dag.order -> t -> t Iter.t
  val iter_dag : t -> t Iter.t
  val map_shallow : store -> (t -> t) -> t -> t
  val iter_shallow : store -> (t -> unit) -> t -> unit
  val pp : t Fmt.printer

  (** {3 Views} *)

  val is_true : t -> bool
  val is_false : t -> bool
  val is_const : t -> bool
  val cc_view : t -> (fun_, t, t Iter.t) CC_view.t

  (* return [Some] iff the term is an undefined constant *)
  val as_fun_undef : t -> (fun_ * Ty.Fun.t) option
  val as_bool : t -> bool option

  (** {3 Store} *)

  val store_size : store -> int
  val store_iter : store -> term Iter.t

  (** {3 Containers} *)

  module Tbl : CCHashtbl.S with type key = t
  module Map : CCMap.S with type key = t
  module Set : CCSet.S with type elt = t
end = struct
  type t = term = {
    mutable term_id: int;
    mutable term_ty: ty;
    term_view: t term_view;
  }

  type 'a view = 'a term_view =
    | Bool of bool
    | App_fun of fun_ * 'a array
    | Eq of 'a * 'a
    | Not of 'a
    | Ite of 'a * 'a * 'a
    | LRA of 'a LRA_view.t
    | LIA of 'a LIA_view.t

  let[@inline] id t = t.term_id
  let[@inline] ty t = t.term_ty
  let[@inline] view t = t.term_view
  let equal = term_equal_
  let hash = term_hash_
  let compare a b = CCInt.compare a.term_id b.term_id

  module H = Hashcons.Make (struct
    type t = term

    let equal t1 t2 = Term_cell.equal t1.term_view t2.term_view
    let hash t = Term_cell.hash t.term_view

    let set_id t id =
      assert (t.term_id < 0);
      t.term_id <- id
  end)

  type store = { tbl: H.t; true_: t lazy_t; false_: t lazy_t }

  let[@inline] make st (c : t term_view) : t =
    let t = { term_id = -1; term_ty = Ty.bool (); term_view = c } in
    let t' = H.hashcons st.tbl t in
    if t == t' then t'.term_ty <- Term_cell.ty c;
    t'

  let[@inline] true_ st = Lazy.force st.true_
  let[@inline] false_ st = Lazy.force st.false_

  let bool st b =
    if b then
      true_ st
    else
      false_ st

  let create ?(size = 1024) () : store =
    let rec st =
      {
        tbl = H.create ~size ();
        true_ = lazy (make st Term_cell.true_);
        false_ = lazy (make st Term_cell.false_);
      }
    in
    ignore (Lazy.force st.true_);
    ignore (Lazy.force st.false_);
    (* not true *)
    st

  let app_fun st f a =
    let cell = Term_cell.app_fun f a in
    make st cell

  let app_fun_l st f l = app_fun st f (CCArray.of_list l)
  let[@inline] const st c = app_fun st c CCArray.empty
  let[@inline] eq st a b = make st (Term_cell.eq a b)
  let[@inline] not_ st a = make st (Term_cell.not_ a)
  let ite st a b c : t = make st (Term_cell.ite a b c)
  let select st sel t : t = app_fun st (Fun.select sel) [| t |]
  let is_a st c t : t = app_fun st (Fun.is_a c) [| t |]
  let app_cstor st c args : t = app_fun st (Fun.cstor c) args

  let[@inline] lra (st : store) (l : t LRA_view.t) : t =
    match l with
    | Var x -> x (* normalize *)
    | _ -> make st (Term_cell.lra l)

  let[@inline] lia (st : store) (l : t LIA_view.t) : t =
    match l with
    | Var x -> x (* normalize *)
    | _ -> make st (Term_cell.lia l)

  module type ARITH_HELPER = sig
    type num

    val plus : store -> t -> t -> t
    val minus : store -> t -> t -> t
    val mult : store -> num -> t -> t
    val const : store -> num -> t
    val leq : store -> t -> t -> t
    val lt : store -> t -> t -> t
    val geq : store -> t -> t -> t
    val gt : store -> t -> t -> t
    val eq : store -> t -> t -> t
    val neq : store -> t -> t -> t
  end

  module LRA = struct
    module V = LRA_view

    let plus st a b : t = lra st (V.Op (Plus, a, b))
    let minus st a b : t = lra st (V.Op (Minus, a, b))
    let mult st a b : t = lra st (V.Mult (a, b))
    let const st q : t = lra st (V.Const q)
    let leq st a b : t = lra st (V.Pred (Leq, a, b))
    let lt st a b : t = lra st (V.Pred (Lt, a, b))
    let geq st a b : t = lra st (V.Pred (Geq, a, b))
    let gt st a b : t = lra st (V.Pred (Gt, a, b))
    let eq st a b : t = lra st (V.Pred (Eq, a, b))
    let neq st a b : t = lra st (V.Pred (Neq, a, b))
  end

  module LIA = struct
    module V = LIA_view

    let plus st a b : t = lia st (V.Op (Plus, a, b))
    let minus st a b : t = lia st (V.Op (Minus, a, b))
    let mult st a b : t = lia st (V.Mult (a, b))
    let const st q : t = lia st (V.Const q)
    let leq st a b : t = lia st (V.Pred (Leq, a, b))
    let lt st a b : t = lia st (V.Pred (Lt, a, b))
    let geq st a b : t = lia st (V.Pred (Geq, a, b))
    let gt st a b : t = lia st (V.Pred (Gt, a, b))
    let eq st a b : t = lia st (V.Pred (Eq, a, b))
    let neq st a b : t = lia st (V.Pred (Neq, a, b))
  end

  let app_undefined store id ty args : t =
    app_fun store (Fun.mk_undef id ty) args

  let const_undefined store id ty : t = const store (Fun.mk_undef_const id ty)

  (* might need to tranfer the negation from [t] to [sign] *)
  let abs tst t : t * bool =
    match view t with
    | Bool false -> true_ tst, false
    | Not u -> u, false
    | App_fun ({ fun_view = Fun_def def; _ }, args) ->
      def.abs ~self:t args (* TODO: pass store *)
    | LRA (Pred (Neq, a, b)) ->
      lra tst (Pred (Eq, a, b)), false (* != is just not eq *)
    | LIA (Pred (Neq, a, b)) ->
      lia tst (Pred (Eq, a, b)), false (* != is just not eq *)
    | _ -> t, true

  let[@inline] is_true t =
    match view t with
    | Bool true -> true
    | _ -> false

  let[@inline] is_false t =
    match view t with
    | Bool false -> true
    | _ -> false

  let[@inline] is_const t =
    match view t with
    | App_fun (_, [||]) -> true
    | _ -> false

  let cc_view (t : t) =
    let module C = CC_view in
    match view t with
    | Bool b -> C.Bool b
    | App_fun (f, _) when not (Fun.do_cc f) -> C.Opaque t (* skip *)
    | App_fun (f, args) -> C.App_fun (f, CCArray.to_iter args)
    | Eq (a, b) -> C.Eq (a, b)
    | Not u -> C.Not u
    | Ite (a, b, c) -> C.If (a, b, c)
    | LRA (Pred (Eq, a, b)) ->
      C.Eq (a, b)
      (* need congruence closure on this one, for theory combination *)
    | LIA (Pred (Eq, a, b)) ->
      C.Eq (a, b)
      (* need congruence closure on this one, for theory combination *)
    | LRA _ | LIA _ -> C.Opaque t
  (* no congruence here *)

  module As_key = struct
    type t = term

    let compare = compare
    let equal = equal
    let hash = hash
  end

  module Map = CCMap.Make (As_key)
  module Set = CCSet.Make (As_key)
  module Tbl = CCHashtbl.Make (As_key)

  (* return [Some] iff the term is an undefined constant *)
  let as_fun_undef (t : term) : (fun_ * Ty.Fun.t) option =
    match view t with
    | App_fun (c, [||]) -> Fun.as_undefined c
    | _ -> None

  let as_bool t =
    match view t with
    | Bool b -> Some b
    | _ -> None

  let pp = pp_term
  let[@inline] iter_shallow _tst f (t : t) : unit = Term_cell.iter f (view t)

  module Iter_dag = struct
    type t = unit Tbl.t
    type order = Pre | Post

    let create () : t = Tbl.create 16

    let iter_dag ?(order = Pre) (self : t) t yield =
      let rec aux t =
        if not @@ Tbl.mem self t then (
          Tbl.add self t ();

          match order with
          | Pre ->
            yield t;
            Term_cell.iter aux (view t)
          | Post ->
            Term_cell.iter aux (view t);
            yield t
        )
      in
      aux t
  end

  let iter_dag_with ~order t yield =
    let st = Iter_dag.create () in
    Iter_dag.iter_dag ~order st t yield

  let iter_dag t yield = iter_dag_with ~order:Pre t yield

  let map_shallow (tst : store) f (t : t) : t =
    match view t with
    | Bool _ -> t
    | App_fun (hd, a) -> app_fun tst hd (CCArray.map f a)
    | Not u -> not_ tst (f u)
    | Eq (a, b) -> eq tst (f a) (f b)
    | Ite (a, b, c) -> ite tst (f a) (f b) (f c)
    | LRA l -> lra tst (LRA_view.map ~f_c:CCFun.id f l)
    | LIA l -> lia tst (LIA_view.map ~f_c:CCFun.id f l)

  let store_size tst = H.size tst.tbl
  let store_iter tst = H.to_iter tst.tbl
end

(** Values (used in models) *)
module Value : sig
  type t = value =
    | V_bool of bool
    | V_element of { id: ID.t; ty: ty }
    | V_cstor of { c: cstor; args: value list }
    | V_custom of {
        view: value_custom_view;
        pp: value_custom_view Fmt.printer;
        eq: value_custom_view -> value_custom_view -> bool;
        hash: value_custom_view -> int;
      }
    | V_real of Q.t

  val true_ : t
  val false_ : t
  val bool : bool -> t
  val real : Q.t -> t
  val real_of_string : string -> t
  val mk_elt : ID.t -> Ty.t -> t
  val is_bool : t -> bool
  val is_true : t -> bool
  val is_false : t -> bool
  val cstor_app : cstor -> t list -> t
  val fresh : Term.t -> t
  val hash : t -> int
  val equal : t -> t -> bool
  val pp : t Fmt.printer
end = struct
  type t = value =
    | V_bool of bool
    | V_element of { id: ID.t; ty: ty }
    | V_cstor of { c: cstor; args: value list }
    | V_custom of {
        view: value_custom_view;
        pp: value_custom_view Fmt.printer;
        eq: value_custom_view -> value_custom_view -> bool;
        hash: value_custom_view -> int;
      }
    | V_real of Q.t

  let true_ = V_bool true
  let false_ = V_bool false

  let[@inline] bool v =
    if v then
      true_
    else
      false_

  let real x = V_real x
  let real_of_string x = V_real (Q.of_string x)
  let mk_elt id ty : t = V_element { id; ty }

  let[@inline] is_bool = function
    | V_bool _ -> true
    | _ -> false

  let[@inline] is_true = function
    | V_bool true -> true
    | _ -> false

  let[@inline] is_false = function
    | V_bool false -> true
    | _ -> false

  let cstor_app c args : t = V_cstor { c; args }
  let equal = eq_value
  let hash = hash_value
  let pp = pp_value
  let fresh (t : term) : t = mk_elt (ID.makef "v_%d" t.term_id) t.term_ty
end

(** Datatypes *)
module Data = struct
  type t = data = {
    data_id: ID.t;
    data_cstors: cstor ID.Map.t lazy_t;
    data_as_ty: ty lazy_t;
  }

  let pp out d = ID.pp out d.data_id
end

(** Datatype selectors.

    A selector is a kind of function that allows to obtain an argument
    of a given constructor. *)
module Select = struct
  type t = select = {
    select_id: ID.t;
    select_cstor: cstor;
    select_ty: ty lazy_t;
    select_i: int;
  }

  let ty sel = Lazy.force sel.select_ty
end

(** Datatype constructors.

    A datatype has one or more constructors, each of which is a special
    kind of function symbol. Constructors are injective and pairwise distinct. *)
module Cstor = struct
  type t = cstor = {
    cstor_id: ID.t;
    cstor_is_a: ID.t;
    mutable cstor_arity: int;
    cstor_args: select list lazy_t;
    cstor_ty_as_data: data;
    cstor_ty: ty lazy_t;
  }

  let id c = c.cstor_id
  let ty_args c = Lazy.force c.cstor_args |> Iter.of_list |> Iter.map Select.ty
  let equal = eq_cstor
  let pp out c = ID.pp out c.cstor_id
end

(* TODO: check-sat-assuming, get-unsat-assumptions, push, pop *)

(** Statements.

    A statement is an instruction for the SMT solver to do something,
    like asserting that a formula is true, declaring a new constant,
    or checking satisfiabilty of the current set of assertions. *)
module Statement = struct
  type t = statement =
    | Stmt_set_logic of string
    | Stmt_set_option of string list
    | Stmt_set_info of string * string
    | Stmt_data of data list
    | Stmt_ty_decl of ID.t * int (* new atomic cstor *)
    | Stmt_decl of ID.t * ty list * ty
    | Stmt_define of definition list
    | Stmt_assert of term
    | Stmt_assert_clause of term list
    | Stmt_check_sat of (bool * term) list
    | Stmt_get_model
    | Stmt_get_value of term list
    | Stmt_exit

  (** Pretty print a statement *)
  let pp out = function
    | Stmt_set_logic s -> Fmt.fprintf out "(set-logic %s)" s
    | Stmt_set_option l ->
      Fmt.fprintf out "(@[set-logic@ %a@])" (Util.pp_list Fmt.string) l
    | Stmt_set_info (a, b) -> Fmt.fprintf out "(@[set-info@ %s@ %s@])" a b
    | Stmt_check_sat [] -> Fmt.string out "(check-sat)"
    | Stmt_check_sat l ->
      let pp_pair out (b, t) =
        if b then
          pp_term out t
        else
          Fmt.fprintf out "(@[not %a@])" pp_term t
      in
      Fmt.fprintf out "(@[check-sat-assuming@ (@[%a@])@])" (Fmt.list pp_pair) l
    | Stmt_ty_decl (s, n) ->
      Fmt.fprintf out "(@[declare-sort@ %a %d@])" ID.pp s n
    | Stmt_decl (id, args, ret) ->
      Fmt.fprintf out "(@[<1>declare-fun@ %a (@[%a@])@ %a@])" ID.pp id
        (Util.pp_list Ty.pp) args Ty.pp ret
    | Stmt_assert t -> Fmt.fprintf out "(@[assert@ %a@])" pp_term t
    | Stmt_assert_clause c ->
      Fmt.fprintf out "(@[assert-clause@ %a@])" (Util.pp_list pp_term) c
    | Stmt_exit -> Fmt.string out "(exit)"
    | Stmt_data l ->
      Fmt.fprintf out "(@[declare-datatypes@ %a@])" (Util.pp_list Data.pp) l
    | Stmt_get_model -> Fmt.string out "(get-model)"
    | Stmt_get_value l ->
      Fmt.fprintf out "(@[get-value@ (@[%a@])@])" (Util.pp_list pp_term) l
    | Stmt_define _ -> assert false
  (* TODO *)
end

*)
