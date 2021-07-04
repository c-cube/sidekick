(** {1 Process Statements} *)

open Sidekick_base

module Solver
  : Sidekick_msat_solver.S with type T.Term.t = Term.t
                            and type T.Term.store = Term.store
                            and type T.Ty.t = Ty.t
                            and type T.Ty.store = Ty.store

val th_bool : Solver.theory
val th_data : Solver.theory
val th_lra : Solver.theory

type 'a or_error = ('a, string) CCResult.t

module Check_cc : sig
  (** theory that check validity of conflicts *)
  val theory : Solver.theory
end

val process_stmt :
  ?hyps:Solver.Atom.t list Vec.t ->
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_cnf:bool ->
  ?dot_proof:string ->
  ?proof_file:string ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Solver.t ->
  Statement.t ->
  unit or_error
