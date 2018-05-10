
(** {1 Process Statements} *)

open Sidekick_smt

type 'a or_error = ('a, string) CCResult.t

(* TODO: record type for config *)

val conv_ty : Ast.Ty.t -> Ty.t

val conv_term : Term.state -> Ast.term -> Term.t

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
  Solver.t ->
  Ast.statement ->
  unit or_error
