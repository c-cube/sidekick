open Sidekick_core
module T = Term

open struct
  let hash_z = Z.hash
  let[@inline] hash_q q = CCHash.combine2 (hash_z (Q.num q)) (hash_z (Q.den q))
end

module Pred = struct
  type t = Sidekick_th_lra.Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  let to_string = function
    | Lt -> "<"
    | Leq -> "<="
    | Neq -> "!=_LRA"
    | Eq -> "=_LRA"
    | Gt -> ">"
    | Geq -> ">="

  let equal : t -> t -> bool = ( = )
  let hash : t -> int = Hashtbl.hash
  let pp out p = Fmt.string out (to_string p)
end

module Op = struct
  type t = Sidekick_th_lra.op = Plus | Minus

  let to_string = function
    | Plus -> "+"
    | Minus -> "-"

  let equal : t -> t -> bool = ( = )
  let hash : t -> int = Hashtbl.hash
  let pp out p = Fmt.string out (to_string p)
end

module View = struct
  include Sidekick_th_lra

  type 'a t = (Q.t, 'a) lra_view

  let map ~f_c f (l : _ t) : _ t =
    match l with
    | LRA_pred (p, a, b) -> LRA_pred (p, f a, f b)
    | LRA_op (p, a, b) -> LRA_op (p, f a, f b)
    | LRA_mult (n, a) -> LRA_mult (f_c n, f a)
    | LRA_const c -> LRA_const (f_c c)
    | LRA_other x -> LRA_other (f x)

  let iter f l : unit =
    match l with
    | LRA_pred (_, a, b) | LRA_op (_, a, b) ->
      f a;
      f b
    | LRA_mult (_, x) | LRA_other x -> f x
    | LRA_const _ -> ()

  let pp ~pp_t out = function
    | LRA_pred (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (Pred.to_string p) pp_t a pp_t b
    | LRA_op (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (Op.to_string p) pp_t a pp_t b
    | LRA_mult (n, x) -> Fmt.fprintf out "(@[*@ %a@ %a@])" Q.pp_print n pp_t x
    | LRA_const q -> Q.pp_print out q
    | LRA_other x -> pp_t out x

  let hash ~sub_hash = function
    | LRA_pred (p, a, b) ->
      Hash.combine4 81 (Hash.poly p) (sub_hash a) (sub_hash b)
    | LRA_op (p, a, b) ->
      Hash.combine4 82 (Hash.poly p) (sub_hash a) (sub_hash b)
    | LRA_mult (n, x) -> Hash.combine3 83 (hash_q n) (sub_hash x)
    | LRA_const q -> Hash.combine2 84 (hash_q q)
    | LRA_other x -> sub_hash x

  let equal ~sub_eq l1 l2 =
    match l1, l2 with
    | LRA_pred (p1, a1, b1), LRA_pred (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | LRA_op (p1, a1, b1), LRA_op (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | LRA_const a1, LRA_const a2 -> Q.equal a1 a2
    | LRA_mult (n1, x1), LRA_mult (n2, x2) -> Q.equal n1 n2 && sub_eq x1 x2
    | LRA_other x1, LRA_other x2 -> sub_eq x1 x2
    | (LRA_pred _ | LRA_op _ | LRA_const _ | LRA_mult _ | LRA_other _), _ ->
      false
end

type term = Term.t
type ty = Term.t
type Const.view += Const of Q.t | Pred of Pred.t | Op of Op.t | Mult_by of Q.t

let ops : Const.ops =
  (module struct
    let pp out = function
      | Const q -> Q.pp_print out q
      | Pred p -> Pred.pp out p
      | Op o -> Op.pp out o
      | Mult_by q -> Fmt.fprintf out "(* %a)" Q.pp_print q
      | _ -> assert false

    let equal a b =
      match a, b with
      | Const a, Const b -> Q.equal a b
      | Pred a, Pred b -> Pred.equal a b
      | Op a, Op b -> Op.equal a b
      | Mult_by a, Mult_by b -> Q.equal a b
      | _ -> false

    let hash = function
      | Const q -> Sidekick_zarith.Rational.hash q
      | Pred p -> Pred.hash p
      | Op o -> Op.hash o
      | Mult_by q -> Hash.(combine2 135 (Sidekick_zarith.Rational.hash q))
      | _ -> assert false
  end)

let real tst = Ty.real tst
let has_ty_real t = Ty.is_real (T.ty t)

let const tst q : term =
  Term.const tst (Const.make (Const q) ops ~ty:(real tst))

let mult_by tst q t : term =
  let ty_c = Term.arrow tst (real tst) (real tst) in
  let c = Term.const tst (Const.make (Mult_by q) ops ~ty:ty_c) in
  Term.app tst c t

let pred tst p t1 t2 : term =
  match p with
  | Pred.Eq -> T.eq tst t1 t2
  | Pred.Neq -> T.not tst (T.eq tst t1 t2)
  | _ ->
    let ty = Term.(arrow_l tst [ real tst; real tst ] (Term.bool tst)) in
    let p = Term.const tst (Const.make (Pred p) ops ~ty) in
    Term.app_l tst p [ t1; t2 ]

let leq tst a b = pred tst Pred.Leq a b
let lt tst a b = pred tst Pred.Lt a b
let geq tst a b = pred tst Pred.Geq a b
let gt tst a b = pred tst Pred.Gt a b
let eq tst a b = pred tst Pred.Eq a b
let neq tst a b = pred tst Pred.Neq a b

let op tst op t1 t2 : term =
  let ty = Term.(arrow_l tst [ real tst; real tst ] (real tst)) in
  let p = Term.const tst (Const.make (Op op) ops ~ty) in
  Term.app_l tst p [ t1; t2 ]

let plus tst a b = op tst Op.Plus a b
let minus tst a b = op tst Op.Minus a b

let view (t : term) : _ View.t =
  let f, args = Term.unfold_app t in
  match T.view f, args with
  | T.E_const { Const.c_view = T.C_eq; _ }, [ _; a; b ] when has_ty_real a ->
    View.LRA_pred (Pred.Eq, a, b)
  | T.E_const { Const.c_view = T.C_not; _ }, [ u ] ->
    (* might be not-eq *)
    let f, args = Term.unfold_app u in
    (match T.view f, args with
    | T.E_const { Const.c_view = T.C_eq; _ }, [ _; a; b ] when has_ty_real a ->
      View.LRA_pred (Pred.Neq, a, b)
    | _ -> View.LRA_other t)
  | T.E_const { Const.c_view = Const q; _ }, [] -> View.LRA_const q
  | T.E_const { Const.c_view = Pred p; _ }, [ a; b ] -> View.LRA_pred (p, a, b)
  | T.E_const { Const.c_view = Op op; _ }, [ a; b ] -> View.LRA_op (op, a, b)
  | T.E_const { Const.c_view = Mult_by q; _ }, [ a ] -> View.LRA_mult (q, a)
  | _ -> View.LRA_other t

let term_of_view store = function
  | View.LRA_const q -> const store q
  | View.LRA_mult (n, t) -> mult_by store n t
  | View.LRA_pred (p, a, b) -> pred store p a b
  | View.LRA_op (o, a, b) -> op store o a b
  | View.LRA_other x -> x
