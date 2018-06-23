(** {2 Literals} *)

open Solver_types

type t = lit = {
  lit_term: term;
  lit_sign : bool
}

val neg : t -> t
val abs : t -> t
val sign : t -> bool
val view : t -> term
val as_atom : t -> term * bool
val dummy : t
val atom : ?sign:bool -> term -> t
val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool
val print : t Fmt.printer
val pp : t Fmt.printer
val norm : t -> t * Sidekick_sat.negated
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t

