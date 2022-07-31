(** Proof terms.

  A proof term is the description of a reasoning step, that yields a clause. *)

open Sidekick_core_logic

type step_id = Proof_step.id
type lit = Lit.t

type data = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
}

type t = unit -> data

include Sidekick_sigs.PRINT with type t := t

val make_data :
  ?lits:lit list ->
  ?terms:Term.t list ->
  ?substs:Subst.t list ->
  ?premises:step_id list ->
  string ->
  data
