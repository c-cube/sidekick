(** Core of the SMT solver using Sidekick_sat

    Sidekick_sat (in src/sat/) is a modular SAT solver in
    pure OCaml.

    This builds a SMT solver on top of it.
*)

module Sigs = Sigs
module Model = Model
module Registry = Registry
module Solver_internal = Solver_internal
module Solver = Solver
module Theory = Theory

type theory = Theory.t
type solver = Solver.t
