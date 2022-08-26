open Sidekick_core
module Pred = Arith_types_.LRA_pred
module Op = Arith_types_.LRA_op
module View = Arith_types_.LRA_view
module T = Term

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

let const tst q : term =
  Term.const tst (Const.make (Const q) ops ~ty:(real tst))

let mult_by tst q t : term =
  let ty_c = Term.arrow tst (real tst) (real tst) in
  let c = Term.const tst (Const.make (Mult_by q) ops ~ty:ty_c) in
  Term.app tst c t

let pred tst p t1 t2 : term =
  let ty = Term.(arrow_l tst [ real tst; real tst ] (Term.bool tst)) in
  let p = Term.const tst (Const.make (Pred p) ops ~ty) in
  Term.app_l tst p [ t1; t2 ]

let op tst op t1 t2 : term =
  let ty = Term.(arrow_l tst [ real tst; real tst ] (real tst)) in
  let p = Term.const tst (Const.make (Op op) ops ~ty) in
  Term.app_l tst p [ t1; t2 ]

let view (t : term) : _ View.t =
  let f, args = Term.unfold_app t in
  match T.view f, args with
  | T.E_const { Const.c_view = Const q; _ }, [] -> View.LRA_const q
  | T.E_const { Const.c_view = Pred p; _ }, [ a; b ] -> View.LRA_pred (p, a, b)
  | T.E_const { Const.c_view = Op op; _ }, [ a; b ] -> View.LRA_op (op, a, b)
  | T.E_const { Const.c_view = Mult_by q; _ }, [ a ] -> View.LRA_mult (q, a)
  | _ -> View.LRA_other t
