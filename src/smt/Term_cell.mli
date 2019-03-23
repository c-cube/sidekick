
open Solver_types

type 'a view = 'a Solver_types.term_view =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | Eq of 'a * 'a
  | If of 'a * 'a * 'a
  | Not of 'a

type t = term view

val equal : t -> t -> bool
val hash : t -> int

val true_ : t
val false_ : t
val const : cst -> t
val app_cst : cst -> term IArray.t -> t
val eq : term -> term -> t
val if_ : term -> term -> term -> t
val not_ : term -> t

val ty : t -> Ty.t
(** Compute the type of this term cell. Not totally free *)

val pp : t Fmt.printer

val iter : ('a -> unit) -> 'a view -> unit

module type ARG = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val pp : t Fmt.printer
end

module Make_eq(X : ARG) : sig
  val equal : X.t view -> X.t view -> bool
  val hash : X.t view -> int
  val pp : X.t view Fmt.printer
end
