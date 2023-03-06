(** Constants.

  Constants are logical symbols, defined by the user thanks to an open type *)

open Types_

type t = const

val name : t -> string
val make : string -> t

include PRINT with type t := t
