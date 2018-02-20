(** {2 Literals} *)

open Solver_types

type t = lit = {
  lit_view : lit_view;
  lit_sign : bool
}

and view = lit_view =
  | Lit_fresh of ID.t
  | Lit_atom of term
  | Lit_expanded of term

val neg : t -> t
val abs : t -> t
val sign : t -> bool
val view : t -> lit_view
val as_atom : t -> (term * bool) option
val fresh_with : ID.t -> t
val fresh : unit -> t
val dummy : t
val atom : ?sign:bool -> term -> t
val cstor_test : Term.state -> data_cstor -> term -> t
val expanded : term -> t
val hash : t -> int
val compare : t -> t -> int
val equal : t -> t -> bool
val print : t Fmt.printer
val pp : t Fmt.printer
val norm : t -> t * Dagon_sat.negated
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t

