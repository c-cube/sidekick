(** Main Signatures.

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
    - a bridge to some SAT solver

    In this module we define most of the main signatures used
    throughout Sidekick.
*)

module Fmt = CCFormat

module type TERM = Sidekick_sigs_term.S
module type LIT = Sidekick_sigs_lit.S
module type PROOF_TRACE = Sidekick_sigs_proof_trace.S

module type SAT_PROOF_RULES = Sidekick_sigs_proof_sat.S
(** Signature for SAT-solver proof emission. *)

module type PROOF_CORE = Sidekick_sigs_proof_core.S
(** Proofs of unsatisfiability. *)
