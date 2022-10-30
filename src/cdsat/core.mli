(** Reasoning core *)

open Sidekick_proof

(** {2 Plugins} *)

module Plugin_action : sig
  type t

  val propagate : t -> TVar.t -> Value.t -> Reason.t -> unit
end

(** Core plugin *)
module Plugin : sig
  type t = private {
    name: string;
    push_level: unit -> unit;
    pop_levels: int -> unit;
    decide: TVar.t -> Value.t option;
    propagate: Plugin_action.t -> TVar.t -> Value.t -> unit;
  }

  val make :
    name:string ->
    push_level:(unit -> unit) ->
    pop_levels:(int -> unit) ->
    decide:(TVar.t -> Value.t option) ->
    propagate:(Plugin_action.t -> TVar.t -> Value.t -> unit) ->
    unit ->
    t
end

(** {2 Basics} *)

type t

val create :
  ?stats:Stat.t ->
  Term.store ->
  TVar.store ->
  proof_tracer:Sidekick_proof.Tracer.t ->
  unit ->
  t
(** Create new solver *)

val tst : t -> Term.store
val vst : t -> TVar.store
val trail : t -> Trail.t
val add_plugin : t -> Plugin.t -> unit
val iter_plugins : t -> Plugin.t Iter.t

(** {2 Solving} *)

val as_asolver : t -> Sidekick_abstract_solver.t

(*
  assert (term -> proof -> unit)
  solve (assumptions:term list -> res)

  as_asolver (-> asolver)

*)
