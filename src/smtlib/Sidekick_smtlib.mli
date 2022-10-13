(** SMTLib-2.6 Driver *)

(** This library provides a parser, a type-checker, and a driver
    for processing SMTLib-2 problems.
*)

type 'a or_error = ('a, string) CCResult.t

module Term = Sidekick_base.Term
module Stmt = Sidekick_base.Statement
module Driver = Driver
module Solver = Solver
module Check_cc = Check_cc

val parse : Term.store -> string -> Stmt.t list or_error
val parse_stdin : Term.store -> Stmt.t list or_error
