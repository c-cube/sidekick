(** {1 Process Statements} *)

open Sidekick_base_term

module Solver
  : Sidekick_msat_solver.S with type A.Term.t = Term.t
                            and type A.Term.state = Term.state
                            and type A.Lit.t = Lit.t
                            and type A.Ty.t = Ty.t

val th_bool : Solver.theory

type 'a or_error = ('a, string) CCResult.t

(* TODO: record type for config *)

val conv_ty : Ast.Ty.t -> Ty.t

val conv_term : Term.state -> Ast.term -> Term.t

val process_stmt :
  ?hyps:Lit.t list Vec.t ->
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
