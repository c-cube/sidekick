(** {1 Sidekick base}

    This library is a starting point for writing concrete implementations
    of SMT solvers with Sidekick.

    It provides a representation of terms, boolean formulas,
    linear arithmetic expressions, datatypes for the functors in Sidekick.

    In addition, it has a notion of {{!Base_types.Statement} Statement}.
    Statements are instructions
    for the SMT solver to do something, such as: define a new constant,
    declare a new constant, assert a formula as being true,
    set an option, check satisfiability of the set of statements added so far,
    etc. Logic formats such as SMT-LIB 2.6 are in fact based on a similar
    notion of statements, and a [.smt2] files contains a list of statements.

    *)

module Term = Sidekick_core.Term
module Base_types = Base_types
module ID = ID
module Stat = Stat
module Value = Base_types.Value
module Term_cell = Base_types.Term_cell
module Statement = Base_types.Statement
module Data = Base_types.Data
module Select = Base_types.Select
module Form = Form
module LRA_view = Base_types.LRA_view
module LRA_pred = Base_types.LRA_pred
module LRA_op = Base_types.LRA_op
module LIA_view = Base_types.LIA_view
module LIA_pred = Base_types.LIA_pred
module LIA_op = Base_types.LIA_op
module Solver_arg = Solver_arg
module Lit = Lit
module Proof = Proof
module Proof_quip = Proof_quip
module Types_ = Types_
