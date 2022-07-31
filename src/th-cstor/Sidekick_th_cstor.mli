(** Theory for constructors *)

open Sidekick_core
module SMT = Sidekick_smt_solver

type ('c, 't) cstor_view = T_cstor of 'c * 't array | T_other of 't

module type ARG = sig
  val view_as_cstor : Term.t -> (Const.t, Term.t) cstor_view
  val lemma_cstor : Lit.t Iter.t -> Proof_term.t
end

val make : (module ARG) -> SMT.theory
