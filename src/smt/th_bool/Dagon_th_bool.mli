
(** {1 Theory of Booleans} *)

open Dagon_smt

type term = Term.t

type 'a builtin =
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a list
  | B_or of 'a list
  | B_imply of 'a list * 'a
  | B_distinct of 'a list

val map_builtin : ('a -> 'b) -> 'a builtin -> 'b builtin
val builtin_to_seq : 'a builtin -> 'a Sequence.t

module T_cell : sig
  type t = Term_cell.t
  val builtin : term builtin -> t
  val and_ : term list -> t
  val or_ : term list -> t
  val not_ : term -> t
  val imply : term list -> term -> t
  val eq : term -> term -> t
  val neq : term -> term -> t
  val distinct : term list -> t
end

val builtin : Term.state -> term builtin -> term
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

val th : Dagon_smt.Theory.t
