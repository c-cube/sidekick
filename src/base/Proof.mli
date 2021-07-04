(** Proofs of unsatisfiability

    Proofs are used in sidekick when the problem is found {b unsatisfiable}.
    A proof collects inferences made by the solver into a list of steps,
    each with its own kind of justification (e.g. "by congruence"),
    and outputs it in some kind of format.

    Currently we target {{: https://c-cube.github.io/quip-book/ } Quip}
    as an experimental proof backend.
*)

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
