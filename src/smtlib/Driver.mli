(** Driver.

  The driver is responsible for processing statements from a SMTLIB file,
  and interacting with the solver based on the statement (asserting formulas,
  calling "solve", etc.)
*)

module Asolver = Solver.Asolver
open Sidekick_base

val th_bool_dyn : Solver.theory
val th_bool_static : Solver.theory
val th_bool : Config.t -> Solver.theory
val th_data : Solver.theory
val th_lra : Solver.theory
val th_ty_unin : Solver.theory

type 'a or_error = ('a, string) CCResult.t

type t
(** The SMTLIB driver *)

val create :
  ?pp_cnf:bool ->
  ?proof_file:string ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Asolver.t ->
  t

val process_stmt : t -> Statement.t -> unit or_error
