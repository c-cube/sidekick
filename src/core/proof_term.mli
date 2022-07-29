(** Proof terms.

  A proof term is the description of a reasoning step, that yields a clause. *)

open Sidekick_core_logic

type step_id = int32
type lit = Lit.t

type t = {
  rule_name: string;
  lit_args: lit Iter.t;
  term_args: Term.t Iter.t;
  subst_args: Subst.t Iter.t;
  premises: step_id Iter.t;
}

include Sidekick_sigs.PRINT with type t := t

val make :
  ?lits:lit Iter.t ->
  ?terms:Term.t Iter.t ->
  ?substs:Subst.t Iter.t ->
  ?premises:step_id Iter.t ->
  string ->
  t
