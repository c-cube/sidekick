(** Theory of Linear Rational Arithmetic *)

open Sidekick_core
module T = Term
module Q = Sidekick_zarith.Rational
open LRA_term

let mk_eq = Form.eq
let mk_bool = T.bool

let theory : Solver.theory =
  Sidekick_th_lra.theory
    (module struct
      module Z = Sidekick_zarith.Int
      module Q = Sidekick_zarith.Rational

      let ty_real = LRA_term.real
      let has_ty_real = LRA_term.has_ty_real
      let view_as_lra = LRA_term.view
      let mk_lra = LRA_term.term_of_view
    end : Sidekick_th_lra.ARG)
