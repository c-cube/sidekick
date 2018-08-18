
open Solver_types

type 'a view = 'a Solver_types.term_view =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | If of 'a * 'a * 'a

type t = term view

val equal : t -> t -> bool
val hash : t -> int

val true_ : t
val false_ : t
val const : cst -> t
val app_cst : cst -> term IArray.t -> t
val if_ : term -> term -> term -> t

val is_value : t -> bool

val ty : t -> Ty.t
(** Compute the type of this term cell. Not totally free *)

val pp : t Fmt.printer

module Tbl : CCHashtbl.S with type key = t

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
