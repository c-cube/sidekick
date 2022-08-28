(** {1 Process Statements} *)

open Sidekick_base
module Solver = Sidekick_base.Solver

val th_bool_dyn : Solver.theory
val th_bool_static : Solver.theory
val th_bool : Config.t -> Solver.theory
val th_data : Solver.theory
val th_lra : Solver.theory
val th_uf : Solver.theory

type 'a or_error = ('a, string) CCResult.t

module Check_cc : sig
  val theory : Solver.theory
  (** theory that check validity of conflicts *)
end

val process_stmt :
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_cnf:bool ->
  ?proof_file:string ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Solver.t ->
  Statement.t ->
  unit or_error
