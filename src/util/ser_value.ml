module Fmt = CCFormat

type t =
  | Null
  | Bool of bool
  | Str of string
  | Bytes of string
  | Int of int
  | List of t list
  | Dict of t Util.Str_map.t

let null = Null
let bool b : t = Bool b
let int i : t = Int i
let string x : t = Str x
let bytes x : t = Bytes x
let list x : t = List x
let dict x : t = Dict x
let dict_of_list l = dict (Util.Str_map.of_list l)

let is_null = function
  | Null -> true
  | _ -> false

let rec pp out (self : t) =
  match self with
  | Null -> Fmt.string out "null"
  | Bool b -> Fmt.bool out b
  | Int i -> Fmt.int out i
  | Str s -> Fmt.Dump.string out s
  | Bytes s -> Fmt.fprintf out "(bytes %S)" s
  | List l -> Fmt.Dump.list pp out l
  | Dict m ->
    Fmt.fprintf out "{@[%a@]}"
      (Util.pp_iter ~sep:", " Fmt.Dump.(pair string pp))
      (Util.Str_map.to_iter m)
