(* TODO


   (** Theory of Linear Rational Arithmetic *)
   module Th_lra = Sidekick_arith_lra.Make (struct
     module S = Solver
     module T = Term
     module Z = Sidekick_zarith.Int
     module Q = Sidekick_zarith.Rational

     type term = S.T.Term.t
     type ty = S.T.Ty.t

     module LRA = Sidekick_arith_lra

     let mk_eq = Form.eq

     let mk_lra store l =
       match l with
       | LRA.LRA_other x -> x
       | LRA.LRA_pred (p, x, y) -> T.lra store (Pred (p, x, y))
       | LRA.LRA_op (op, x, y) -> T.lra store (Op (op, x, y))
       | LRA.LRA_const c -> T.lra store (Const c)
       | LRA.LRA_mult (c, x) -> T.lra store (Mult (c, x))

     let mk_bool = T.bool

     let rec view_as_lra t =
       match T.view t with
       | T.LRA l ->
         let module LRA = Sidekick_arith_lra in
         (match l with
         | Const c -> LRA.LRA_const c
         | Pred (p, a, b) -> LRA.LRA_pred (p, a, b)
         | Op (op, a, b) -> LRA.LRA_op (op, a, b)
         | Mult (c, x) -> LRA.LRA_mult (c, x)
         | To_real x -> view_as_lra x
         | Var x -> LRA.LRA_other x)
       | T.Eq (a, b) when Ty.equal (T.ty a) (Ty.real ()) -> LRA.LRA_pred (Eq, a, b)
       | _ -> LRA.LRA_other t

     let ty_lra _st = Ty.real ()
     let has_ty_real t = Ty.equal (T.ty t) (Ty.real ())
     let lemma_lra = Proof.lemma_lra

     module Gensym = Gensym
   end)
*)
