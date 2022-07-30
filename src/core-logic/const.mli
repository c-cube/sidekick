(** Constants.

  Constants are logical symbols, defined by the user thanks to an open type *)

open Types_

type t = const
type view = const_view = ..

module type DYN_OPS = sig
  val pp : view Fmt.printer
  val equal : view -> view -> bool
  val hash : view -> int
end

type ops = (module DYN_OPS)

val view : t -> view
val make : view -> ops -> ty:term -> t
val ty : t -> term

include EQ_HASH_PRINT with type t := t