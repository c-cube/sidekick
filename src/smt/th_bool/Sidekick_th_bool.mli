
(** {1 Theory of Booleans} *)

open Sidekick_smt

type term = Term.t

type 'a view = private
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a IArray.t
  | B_or of 'a IArray.t
  | B_imply of 'a IArray.t * 'a
  | B_distinct of 'a IArray.t
  | B_atom of 'a

val view : term -> term view

val and_ : Term.state -> term -> term -> term
val or_ : Term.state -> term -> term -> term
val not_ : Term.state -> term -> term
val imply : Term.state -> term list -> term -> term
val eq : Term.state -> term -> term -> term
val neq : Term.state -> term -> term -> term
val distinct : Term.state -> term list -> term
val and_l : Term.state -> term list -> term
val or_l : Term.state -> term list -> term

module Lit : sig
  type t = Lit.t
  val eq : Term.state -> term -> term -> t
  val neq : Term.state -> term -> term -> t
end

val th : Sidekick_smt.Theory.t
