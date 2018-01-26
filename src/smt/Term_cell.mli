
open CDCL
open Solver_types

type t = term term_cell

val equal : t -> t -> bool
val hash : t -> int

val true_ : t
val const : cst -> t
val app_cst : cst -> term IArray.t -> t
val cstor_test : data_cstor -> term -> t
val cstor_proj : data_cstor -> int -> term -> t
val case : term -> term ID.Map.t -> t
val if_ : term -> term -> term -> t
val builtin : term builtin -> t
val and_ : term -> term -> t
val or_ : term -> term -> t
val not_ : term -> t
val imply : term -> term -> t
val eq : term -> term -> t

val ty : t -> Ty.t
(** Compute the type of this term cell. Not totally free *)

module Tbl : CCHashtbl.S with type key = t

module type ARG = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module Make_eq(X : ARG) : sig
  val equal : X.t term_cell -> X.t term_cell -> bool
  val hash : X.t term_cell -> int
end
