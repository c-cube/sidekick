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
