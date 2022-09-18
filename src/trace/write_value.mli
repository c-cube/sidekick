(** Value writer.

    A [Writer.t] value, describes how to write some structured
    data into a {!Sink.t}. It reflects the shape of the structured
    data but does not commit to a particular serialization format.
*)

type t = private
  | Bool of bool
  | Str of string
  | Bytes of string
  | Int of int
  | List of delayed list
  | Dict of (string * delayed) list

and delayed = unit -> t

val bool : bool -> t
val int : int -> t
val string : string -> t
val bytes : string -> t
val list : delayed list -> t
val dict : (string * delayed) list -> t
