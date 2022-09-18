(** Value writer.

    A [Writer.t] value, describes how to write some structured
    data into a {!Sink.t}. It reflects the shape of the structured
    data but does not commit to a particular serialization format.
*)

type t =
  | Bool of bool
  | Str of string
  | Bytes of string
  | Int of int
  | List of delayed list
  | Dict of (string * delayed) list

and delayed = unit -> t

let bool b : t = Bool b
let int i : t = Int i
let string x : t = Str x
let bytes x : t = Bytes x
let list x : t = List x
let dict x : t = Dict x
