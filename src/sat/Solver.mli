module type S = Solver_intf.S
(** Safe external interface of solvers. *)

module Pure_sat : S with type theory = unit
module Make_cdcl_t (Th : Solver_intf.PLUGIN_CDCL_T) : S with type theory = Th.t
