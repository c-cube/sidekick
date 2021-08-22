
(** Dummy proof module that does nothing. *)

open Base_types

include Sidekick_core.PROOF
  with type lit = Lit.t
   and type term = Term.t

val create : unit -> t

val lemma_bool_tauto : Lit.t Iter.t -> t -> unit
val lemma_bool_c : string -> term list -> t -> unit
val lemma_bool_equiv : term -> term -> t -> unit
val lemma_ite_true : a:term -> ite:term -> t -> unit
val lemma_ite_false : a:term -> ite:term -> t -> unit

val lemma_lra : Lit.t Iter.t -> t -> unit

val lemma_isa_split : Lit.t Iter.t -> t -> unit
val lemma_isa_disj : Lit.t Iter.t -> t -> unit
val lemma_cstor_inj : Lit.t Iter.t -> t -> unit
