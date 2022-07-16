(** Proof rules for common operations and congruence closure *)

module type S = sig
  type rule
  type term
  type lit

  type step_id
  (** Identifier for a proof proof_rule (like a unique ID for a clause previously
      added/proved) *)

  val lemma_cc : lit Iter.t -> rule
  (** [lemma_cc proof lits] asserts that [lits] form a tautology for the theory
      of uninterpreted functions. *)

  val define_term : term -> term -> rule
  (** [define_term cst u proof] defines the new constant [cst] as being equal
      to [u].
      The result is a proof of the clause [cst = u] *)

  val proof_p1 : step_id -> step_id -> rule
  (** [proof_p1 p1 p2], where [p1] proves the unit clause [t=u] (t:bool)
      and [p2] proves [C \/ t], is the rule that produces [C \/ u],
      i.e unit paramodulation. *)

  val proof_r1 : step_id -> step_id -> rule
  (** [proof_r1 p1 p2], where [p1] proves the unit clause [|- t] (t:bool)
      and [p2] proves [C \/ ¬t], is the rule that produces [C \/ u],
      i.e unit resolution. *)

  val proof_res : pivot:term -> step_id -> step_id -> rule
  (** [proof_res ~pivot p1 p2], where [p1] proves the clause [|- C \/ l]
      and [p2] proves [D \/ ¬l], where [l] is either [pivot] or [¬pivot],
      is the rule that produces [C \/ D], i.e boolean resolution. *)

  val with_defs : step_id -> step_id Iter.t -> rule
  (** [with_defs pr defs] specifies that [pr] is valid only in
      a context where the definitions [defs] are present. *)

  val lemma_true : term -> rule
  (** [lemma_true (true) p] asserts the clause [(true)] *)

  val lemma_preprocess : term -> term -> using:step_id Iter.t -> rule
  (** [lemma_preprocess t u ~using p] asserts that [t = u] is a tautology
      and that [t] has been preprocessed into [u].

      The theorem [/\_{eqn in using} eqn |- t=u] is proved using congruence
      closure, and then resolved against the clauses [using] to obtain
      a unit equality.

      From now on, [t] and [u] will be used interchangeably.
      @return a rule ID for the clause [(t=u)]. *)

  val lemma_rw_clause :
    step_id -> res:lit Iter.t -> using:step_id Iter.t -> rule
  (** [lemma_rw_clause prc ~res ~using], where [prc] is the proof of [|- c],
      uses the equations [|- p_i = q_i] from [using]
      to rewrite some literals of [c] into [res]. This is used to preprocess
      literals of a clause (using {!lemma_preprocess} individually). *)
end

type ('rule, 'step_id, 'term, 'lit) t =
  (module S
     with type rule = 'rule
      and type step_id = 'step_id
      and type term = 'term
      and type lit = 'lit)

(** Make a dummy proof with given types *)
module Dummy (A : sig
  type rule
  type step_id
  type term
  type lit

  val dummy_rule : rule
end) :
  S
    with type rule = A.rule
     and type step_id = A.step_id
     and type term = A.term
     and type lit = A.lit = struct
  include A

  let lemma_cc _ = dummy_rule
  let define_term _ _ = dummy_rule
  let proof_p1 _ _ = dummy_rule
  let proof_r1 _ _ = dummy_rule
  let proof_res ~pivot:_ _ _ = dummy_rule
  let with_defs _ _ = dummy_rule
  let lemma_true _ = dummy_rule
  let lemma_preprocess _ _ ~using:_ = dummy_rule
  let lemma_rw_clause _ ~res:_ ~using:_ = dummy_rule
end
