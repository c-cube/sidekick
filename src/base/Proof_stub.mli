
(** Dummy proof module that does nothing. *)

open Base_types

include Sidekick_core.PROOF
  with type lit = Lit.t
   and type term = Term.t

val create : unit -> t

val lemma_bool_tauto : t -> Lit.t Iter.t -> unit
val lemma_bool_c : t -> string -> term list -> unit
val lemma_bool_equiv : t -> term -> term -> unit
val lemma_ite_true : t -> a:term -> ite:term -> unit
val lemma_ite_false : t -> a:term -> ite:term -> unit

val lemma_lra : t -> Lit.t Iter.t -> unit

val lemma_isa_split : t -> Lit.t Iter.t -> unit
val lemma_isa_disj : t -> Lit.t Iter.t -> unit
val lemma_cstor_inj : t -> Lit.t Iter.t -> unit
