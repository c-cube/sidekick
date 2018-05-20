

exception Error of string

val errorf : ('a, Format.formatter, unit, 'b) format4 -> 'a
(** @raise Error when called *)
