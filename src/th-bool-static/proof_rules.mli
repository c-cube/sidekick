open Sidekick_core

type term = Term.t
type lit = Lit.t

val lemma_bool_tauto : lit list -> Proof_term.t
(** Boolean tautology lemma (clause) *)

val lemma_bool_c : string -> term list -> Proof_term.t
(** Basic boolean logic lemma for a clause [|- c].
      [proof_bool_c b name cs] is the Proof_term.t designated by [name]. *)

val lemma_bool_equiv : term -> term -> Proof_term.t
(** Boolean tautology lemma (equivalence) *)

val lemma_ite_true : ite:term -> Proof_term.t
(** lemma [a ==> ite a b c = b] *)

val lemma_ite_false : ite:term -> Proof_term.t
(** lemma [¬a ==> ite a b c = c] *)
