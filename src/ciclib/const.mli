(** Constants.

  Constants are logical symbols, defined by the user thanks to an open type *)

open Types_

type t = const

val name : t -> string
val make : string -> ty:term -> t
val ty : t -> term

include PRINT with type t := t
