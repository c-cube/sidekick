exception Error of string

val errorf : ('a, Format.formatter, unit, 'b) format4 -> 'a
(** @raise Error when called *)

type nonrec 'a result = ('a, string) result

val try_ : (unit -> 'a) -> 'a result
