(** Basic string constants.

   These constants are a string name, coupled with a type.
*)

open Types_

type const_view += private Str of string

val const_decoders : Const.decoders
val make : string -> ty:term -> const
