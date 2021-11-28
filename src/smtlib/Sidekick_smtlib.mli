(** {1 SMTLib-2 Interface} *)

(** This library provides a parser, a type-checker, and a solver interface
    for processing SMTLib-2 problems.
*)

type 'a or_error = ('a, string) CCResult.t

module Term = Sidekick_base.Term
module Stmt = Sidekick_base.Statement
module Process = Process
module Solver = Process.Solver
module Proof = Sidekick_base.Proof

val parse : Term.store -> string -> Stmt.t list or_error

val parse_stdin : Term.store -> Stmt.t list or_error
