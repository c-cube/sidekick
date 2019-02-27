
type 'a view = 'a Bool_intf.view

type term = Sidekick_smt.Term.t

include Bool_intf.BOOL_TERM
  with type t = term
   and type state = Sidekick_smt.Term.state

val and_ : state -> term -> term -> term
val or_ : state -> term -> term -> term
val not_ : state -> term -> term
val imply : state -> term -> term -> term
val imply_a : state -> term IArray.t -> term -> term
val imply_l : state -> term list -> term -> term
val eq : state -> term -> term -> term
val neq : state -> term -> term -> term
val and_a : state -> term IArray.t -> term
val and_l : state -> term list -> term
val or_a : state -> term IArray.t -> term
val or_l : state -> term list -> term
