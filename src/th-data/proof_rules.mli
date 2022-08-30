open Sidekick_core

val lemma_isa_cstor : cstor_t:Term.t -> Term.t -> Proof_term.t
(** [lemma_isa_cstor (d …) (is-c t)] returns the clause
      [(c …) = t |- is-c t] or [(d …) = t |- ¬ (is-c t)] *)

val lemma_select_cstor : cstor_t:Term.t -> Term.t -> Proof_term.t
(** [lemma_select_cstor (c t1…tn) (sel-c-i t)]
      returns a proof of [t = c t1…tn |- (sel-c-i t) = ti] *)

val lemma_isa_split : Term.t -> Lit.t list -> Proof_term.t
(** [lemma_isa_split t lits] is the proof of
      [is-c1 t \/ is-c2 t \/ … \/ is-c_n t] *)

val lemma_isa_sel : Term.t -> Proof_term.t
(** [lemma_isa_sel (is-c t)] is the proof of
      [is-c t |- t = c (sel-c-1 t)…(sel-c-n t)] *)

val lemma_isa_disj : Lit.t -> Lit.t -> Proof_term.t
(** [lemma_isa_disj (is-c t) (is-d t)] is the proof
      of [¬ (is-c t) \/ ¬ (is-c t)] *)

val lemma_cstor_inj : Term.t -> Term.t -> int -> Proof_term.t
(** [lemma_cstor_inj (c t1…tn) (c u1…un) i] is the proof of
      [c t1…tn = c u1…un |- ti = ui] *)

val lemma_cstor_distinct : Term.t -> Term.t -> Proof_term.t
(** [lemma_isa_distinct (c …) (d …)] is the proof
      of the unit clause [|- (c …) ≠ (d …)] *)

val lemma_acyclicity : (Term.t * Term.t) list -> Proof_term.t
(** [lemma_acyclicity pairs] is a proof of [t1=u1, …, tn=un |- false]
      by acyclicity. *)
