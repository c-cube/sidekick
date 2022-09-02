open Sidekick_core

type ty = Term.t

module type ARG = sig
  val ty_is_unin : ty -> bool
end

val theory : (module ARG) -> Sidekick_smt_solver.Theory.t
(** Theory of uninterpreted types *)
