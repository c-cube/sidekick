(** {1 SMTLib-2 Interface} *)

(** This library provides a parser, a type-checker, and a solver interface
    for processing SMTLib-2 problems.
*)

type 'a or_error = ('a, string) CCResult.t

module Ast = Ast
module Process = Process
module Solver = Process.Solver

val parse : string -> Ast.statement list or_error

val parse_stdin : unit -> Ast.statement list or_error
