(** {1 Process Statements} *)

open Sidekick_base

module Solver
  : Sidekick_smt_solver.S with type T.Term.t = Term.t
                            and type T.Term.store = Term.store
                            and type T.Ty.t = Ty.t
                            and type T.Ty.store = Ty.store
                            and type proof = Proof_dummy.t

val th_bool : Solver.theory
val th_data : Solver.theory
val th_lra : Solver.theory

type 'a or_error = ('a, string) CCResult.t

module Check_cc : sig
  (** theory that check validity of conflicts *)
  val theory : Solver.theory
end

val process_stmt :
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_cnf:bool ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Solver.t ->
  Statement.t ->
  unit or_error
