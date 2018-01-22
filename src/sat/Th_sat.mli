
(** The module defining formulas *)

(** SAT Formulas

    This modules implements formuals adequate for use in a pure SAT Solver.
    Atomic formulas are represented using integers, that should allow
    near optimal efficiency (both in terms of space and time).
*)

open Msat

include Theory_intf.S with type formula = int and type proof = unit
(** This modules implements the requirements for implementing an SAT Solver. *)

val make : t -> int -> formula
(** Make a proposition from an integer. *)

val fresh : t -> formula
(** Make a fresh atom *)

val sign : formula -> bool
(** Is the given atom positive ? *)

val apply_sign : bool -> formula -> formula
(** [apply_sign b] is the identity if [b] is [true], and the negation
    function if [b] is [false]. *)

val set_sign : bool -> formula -> formula
(** Return the atom with the sign set. *)

