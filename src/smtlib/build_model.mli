open Common_
open! Sidekick_base

type t

val create : unit -> t
val add_ty : t -> Term.t -> unit
val add_fun : t -> Term.t -> unit
val build : t -> Solver.sat_result -> Model.t
