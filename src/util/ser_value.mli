(** Serialization representation.

    A [Ser_value.t] describes how to serialized some structured
    data into bytes.
    It reflects the shape of the structured data but does not commit to a
    particular serialization format.
*)

type t = private
  | Bool of bool
  | Str of string
  | Bytes of string
  | Int of int
  | List of t list
  | Dict of t Util.Str_map.t

val bool : bool -> t
val int : int -> t
val string : string -> t
val bytes : string -> t
val list : t list -> t
val dict : t Util.Str_map.t -> t
val dict_of_list : (string * t) list -> t
