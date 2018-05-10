
(** {1 Main for dimacs} *)

(** This library provides a parser for DIMACS files, to represent
    SAT problems.

    http://www.satcompetition.org/2009/format-benchmarks2009.html
*)

type 'a or_error = ('a, string) CCResult.t

val parse : string -> int list list or_error
(** Parse a file into a list of clauses. *)
