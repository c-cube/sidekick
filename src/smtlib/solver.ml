module Asolver = Sidekick_abstract_solver.Asolver
module Smt_solver = Sidekick_smt_solver

type t = Asolver.t
type cdcl_theory = Smt_solver.theory
