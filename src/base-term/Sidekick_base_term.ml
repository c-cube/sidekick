
module ID = ID
module Ty_card = Ty_card
module Cst = Cst
module Stat = Stat
module Model = Model
module Ast = Ast
module Term = Term
module Value = Value
module Term_cell = Term_cell
module Ty = Ty
module Lit = Lit
module Value = Value


module Arg
  : Sidekick_core.TERM_LIT
    with type Term.t = Term.t
     and type Lit.t = Lit.t
     and type Fun.t = Cst.t
     and type Ty.t = Ty.t
= struct
  module Term = Term
  module Lit = Lit
  module Fun = Cst
  module Ty = Ty
end
