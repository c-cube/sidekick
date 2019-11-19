(** {1 SMTLib-2 Interface} *)

(** This library provides a parser, a type-checker, and a solver interface
    for processing SMTLib-2 problems.
*)

type 'a or_error = ('a, string) CCResult.t

module Term = Sidekick_base_term.Term
module Stmt = Sidekick_base_term.Statement
module Process = Process
module Solver = Process.Solver

val parse : Term.state -> string -> Stmt.t list or_error

val parse_stdin : Term.state -> Stmt.t list or_error
