(*

include Sidekick_cc.S
  with type term = Term.t
   and type model = Model.t
   and type lit = Lit.t
   and type fun_ = Cst.t
   and type term_state = Term.state
   and type proof = Solver_types.proof
   and module Key = Sidekick_cc.Key

*)
module Mini_cc : Sidekick_cc.Mini_cc.S
  with type term = Term.t
   and type fun_ = Cst.t
   and type term_state = Term.state
