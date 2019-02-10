
module Arg = struct
  module Fun = Cst
  module Term = Term
  module Lit = Lit
  module Value = Value
  module Ty = Ty
  module Model = Model
  module Proof = struct
    type t = Solver_types.proof
    let pp = Solver_types.pp_proof
    let default = Solver_types.Proof_default
  end
end

include Sidekick_cc.Make(Arg)

module Mini_cc = Sidekick_cc.Mini_cc.Make(Arg)
