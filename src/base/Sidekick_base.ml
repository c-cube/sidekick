(** {1 Sidekick base}

    This library is a starting point for writing concrete implementations
    of SMT solvers with Sidekick.

    It provides a representation of terms, boolean formulas,
    linear arithmetic expressions, datatypes for the functors in Sidekick.

    In addition, it has a notion of {!Statement}. Statements are instructions
    for the SMT solver to do something, such as: define a new constant,
    declare a new constant, assert a formula as being true,
    set an option, check satisfiability of the set of statements added so far,
    etc. Logic formats such as SMT-LIB 2.6 are in fact based on a similar
    notion of statements, and a [.smt2] files contains a list of statements.

    *)


module Base_types = Base_types
module ID = ID
module Fun = Base_types.Fun
module Stat = Stat
module Model = Model
module Term = Base_types.Term
module Value = Base_types.Value
module Term_cell = Base_types.Term_cell
module Ty = Base_types.Ty
module Statement = Base_types.Statement
module Data = Base_types.Data
module Select = Base_types.Select
module Proof = Proof

module Arg
  : Sidekick_core.TERM
    with type Term.t = Term.t
     and type Fun.t = Fun.t
     and type Ty.t = Ty.t
     and type Term.state = Term.state
= struct
  module Term = Term
  module Fun = Fun
  module Ty = Ty
end
