(** Proof terms.

  A proof term is the description of a reasoning step, that yields a clause. *)

open Sidekick_core_logic

type step_id = Proof_step.id
type local_ref = int
type lit = Lit.t

type rule_apply = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
}

type t =
  | P_ref of step_id
  | P_local of local_ref  (** Local reference, in a let *)
  | P_let of (local_ref * t) list * t
  | P_apply of rule_apply

type delayed = unit -> t

include Sidekick_sigs.PRINT with type t := t

val ref_ : step_id -> t
val local_ref : local_ref -> t
val let_ : (local_ref * t) list -> t -> t

val apply_rule :
  ?lits:lit list ->
  ?terms:Term.t list ->
  ?substs:Subst.t list ->
  ?premises:step_id list ->
  string ->
  t
