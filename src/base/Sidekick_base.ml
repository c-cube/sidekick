(** Sidekick base

    This library is a starting point for writing concrete implementations
    of SMT solvers with Sidekick.

    It provides a representation of terms, boolean formulas,
    linear arithmetic expressions, datatypes for the functors in Sidekick.

    In addition, it has a notion of {{!Statement.t} Statement}.
    Statements are instructions
    for the SMT solver to do something, such as: define a new constant,
    declare a new constant, assert a formula as being true,
    set an option, check satisfiability of the set of statements added so far,
    etc. Logic formats such as SMT-LIB 2.6 are in fact based on a similar
    notion of statements, and a [.smt2] files contains a list of statements.

*)

module Types_ = Types_
module Term = Term
module Const = Sidekick_core.Const
module Ty = Ty
module ID = ID
module Form = Form
module Data_ty = Data_ty
module Cstor = Data_ty.Cstor
module Select = Data_ty.Select
module Statement = Statement
module Solver = Solver
module Uconst = Uconst
module Config = Config
module LRA_term = LRA_term
module Th_data = Th_data
module Th_bool = Th_bool
module Th_lra = Th_lra
module Th_ty_unin = Th_ty_unin

let k_th_bool_config = Th_bool.k_config
let th_bool = Th_bool.theory
let th_bool_dyn : Solver.theory = Th_bool.theory_dyn
let th_bool_static : Solver.theory = Th_bool.theory_static
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
let th_ty_unin : Solver.theory = Th_ty_unin.theory
