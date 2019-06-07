module Base_types = Base_types
module ID = ID
module Ty_card = Base_types.Ty_card
module Fun = Base_types.Fun
module Stat = Stat
module Model = Model
module Term = Base_types.Term
module Value = Base_types.Value
module Term_cell = Base_types.Term_cell
module Ty = Base_types.Ty
module Lit = Base_types.Lit

module Arg
  : Sidekick_core.TERM_LIT
    with type Term.t = Term.t
     and type Lit.t = Lit.t
     and type Fun.t = Fun.t
     and type Ty.t = Ty.t
= struct
  module Term = Term
  module Lit = Lit
  module Fun = Fun
  module Ty = Ty
end
