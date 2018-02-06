
(** {1 SMTLib-2 Interface} *)

(** This library provides a parser, a type-checker, and a solver interface
    for processing SMTLib-2 problems.
*)

type 'a or_error = ('a, string) CCResult.t

module Ast = Ast

val parse : string -> Dagon_smt.Ast.statement list or_error

val parse_stdin : unit -> Dagon_smt.Ast.statement list or_error

val conv_bool_term : Dagon_smt.Term.state -> Dagon_smt.Ast.term -> Dagon_smt.Lit.t list list
(** Convert a boolean term into CNF *)

val process_stmt :
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_cnf:bool ->
  ?dot_proof:string ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Dagon_smt.Solver.t ->
  Dagon_smt.Ast.statement ->
  unit or_error
(** Process the given statement.
    @raise Incorrect_model if model is not correct
*)
