(** Signature for the main SMT solver types.

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
    - a bridge to some SAT solver

    In this module we collect signatures defined elsewhere and define
    the module types for the main SMT solver.
*)

include Sidekick_core
module Model = Sidekick_model
module Simplify = Sidekick_simplify
module CC = Sidekick_cc.CC
module E_node = Sidekick_cc.E_node
module CC_expl = Sidekick_cc.Expl
module Proof = Sidekick_proof

type term = Term.t
type ty = term
type value = Term.t
type lit = Lit.t
type term_store = Term.store
type step_id = Sidekick_proof.Step.id

(* actions from the sat solver *)
type sat_acts = Sidekick_sat.acts

type th_combination_conflict = {
  lits: lit list;
  semantic: (bool * term * term) list;
      (* set of semantic eqns/diseqns (ie true only in current model) *)
}
(** Conflict obtained during theory combination. It involves equalities
      merged because of the current model so it's not a "true" conflict
      and doesn't need to kill the current trail. *)

(** Argument to pass to the functor {!Make} in order to create a
    new Msat-based SMT solver. *)
module type ARG = sig
  val view_as_cc : Sidekick_cc.view_as_cc
end
