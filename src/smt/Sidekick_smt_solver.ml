(** Core of the SMT solver using Sidekick_sat

    Sidekick_sat (in src/sat/) is a modular SAT solver in
    pure OCaml.

    This builds a SMT solver on top of it.
*)

module Sigs = Sigs
module Model_builder = Model_builder
module Registry = Registry
module Solver_internal = Solver_internal
module Solver = Solver
module Model = Model
module Theory = Theory
module Theory_id = Theory_id
module Preprocess = Preprocess
module Find_foreign = Find_foreign
module Tracer = Tracer
module Trace_reader = Trace_reader

type theory = Theory.t
type solver = Solver.t
