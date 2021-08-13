
module type S = Solver_intf.S
(** Safe external interface of solvers. *)

module Make_pure_sat(Th: Solver_intf.PLUGIN_SAT)
  : S with module Formula = Th.Formula
       and type lemma = Th.lemma
       and type proof = Th.proof
       and type theory = unit

module Make_cdcl_t(Th : Solver_intf.PLUGIN_CDCL_T)
  : S with module Formula = Th.Formula
       and type lemma = Th.lemma
       and type proof = Th.proof
       and type theory = Th.t
