(** {1 DIMACS parser} *)

type t

val create : in_channel -> t

val parse_header : t -> int*int

val next_clause : t -> int list option

val iter : t -> int list Iter.t


