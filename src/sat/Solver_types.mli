
(** Internal types (implementation)

    This modules actually implements the internal types used by the solver.
    Since mutation is heavily used in the solver, it is really, really, *really*
    discouraged to direclty use the functions in this module if you don't know the
    inner working of mSAT perfectly as even the simplest
    change can have dramatic effects on the solver.
*)

module type S = Solver_types_intf.S
(** Interface for the internal types. *)

module Var_fields = Solver_types_intf.Var_fields

module Make (E : Theory_intf.S):
  S with type formula = E.formula
     and type proof = E.proof
(** Functor to instantiate the types of clauses for a solver. *)

