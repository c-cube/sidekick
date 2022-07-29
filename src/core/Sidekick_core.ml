(** Main Signatures.

    Theories and concrete solvers rely on an environment that defines
    several important types:

      - types
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
    - a bridge to some SAT solver

    In this module we define most of the main signatures used
    throughout Sidekick.
*)

module Fmt = CCFormat

(* re-export *)

module Const = Sidekick_core_logic.Const

module Term = struct
  include Sidekick_core_logic.Term
  include Sidekick_core_logic.T_builtins
end

module Bvar = Sidekick_core_logic.Bvar
module Lit = Lit
module Proof_core = Proof_core
module Proof_sat = Proof_sat
module Proof_trace = Proof_trace
module Proof_term = Proof_term
module Subst = Sidekick_core_logic.Subst
module Var = Sidekick_core_logic.Var
