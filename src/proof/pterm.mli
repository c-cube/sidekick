(** Proof terms.

  A proof term is the description of a reasoning step, that yields a clause. *)

type step_id = Step.id
type lit = Lit.t

type local_ref = Step.id
(** A local reference is a step id that is only valid in the scope
    of a {!P_let}. Typically one can use negative integers to avoid
    accidental shadowing. *)

type rule_apply = {
  rule_name: string;
  lit_args: lit list;
  term_args: Term.t list;
  subst_args: Subst.t list;
  premises: step_id list;
  indices: int list;
}

type t =
  | P_ref of step_id
  | P_local of local_ref  (** Local reference, in a let *)
  | P_let of (local_ref * t) list * t
  | P_apply of rule_apply

type delayed = unit -> t

include Sidekick_sigs.PRINT with type t := t

val ref : step_id -> t
val local_ref : local_ref -> t
val let_ : (local_ref * t) list -> t -> t
val delay : (unit -> t) -> delayed

val dummy : t
(** Reference to the dummy step *)

val apply_rule :
  ?lits:lit list ->
  ?terms:Term.t list ->
  ?substs:Subst.t list ->
  ?premises:step_id list ->
  ?indices:int list ->
  string ->
  t

val to_ser : Term.Tracer.t -> t -> Ser_value.t
(** Serialize *)

val deser : Term.Trace_reader.t -> t Ser_decode.t
