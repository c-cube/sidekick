type t =
  | Bool of bool
  | Str of string
  | Bytes of string
  | Int of int
  | List of t list
  | Dict of t Util.Str_map.t

let bool b : t = Bool b
let int i : t = Int i
let string x : t = Str x
let bytes x : t = Bytes x
let list x : t = List x
let dict x : t = Dict x
let dict_of_list l = dict (Util.Str_map.of_list l)
