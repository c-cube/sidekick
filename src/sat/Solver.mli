module type S = Solver_intf.S
(** Safe external interface of solvers. *)

module Make_pure_sat (Th : Solver_intf.PLUGIN_SAT) :
  S
    with module Lit = Th.Lit
     and module Proof_trace = Th.Proof_trace
     and module Proof_rules = Th.Proof_rules
     and type theory = unit

module Make_cdcl_t (Th : Solver_intf.PLUGIN_CDCL_T) :
  S
    with module Lit = Th.Lit
     and module Proof_trace = Th.Proof_trace
     and module Proof_rules = Th.Proof_rules
     and type theory = Th.t
