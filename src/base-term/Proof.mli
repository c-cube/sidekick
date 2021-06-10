open Base_types

include Sidekick_core.PROOF
  with type term = Term.t
   and type ty = Ty.t

val isa_split : ty -> term Iter.t -> t
val isa_disj : ty -> term -> term -> t
val cstor_inj : Cstor.t -> int -> term list -> term list -> t

val bool_eq : term -> term -> t
val bool_c : string -> term list -> t
val ite_true : term -> t
val ite_false : term -> t

val lra : lit Iter.t -> t
val lra_l : lit list -> t
