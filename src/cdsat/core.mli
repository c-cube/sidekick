(** Reasoning core *)

open Sidekick_proof
module Check_res = Sidekick_abstract_solver.Check_res

(** Argument to the solver *)
module type ARG = sig
  val or_l : Term.store -> Term.t list -> Term.t
  (** build a disjunction *)
end

(** {2 Plugins} *)

module Plugin_action : sig
  type t

  val propagate : t -> TVar.t -> Value.t -> Reason.t -> unit
  val term_to_var : t -> Term.t -> TVar.t
end

(** Core plugin *)
module Plugin : sig
  type t
  type builder

  val name : t -> string

  val make_builder :
    name:string ->
    create:(TVar.store -> 'st) ->
    push_level:('st -> unit) ->
    pop_levels:('st -> int -> unit) ->
    decide:('st -> TVar.t -> Value.t option) ->
    propagate:('st -> Plugin_action.t -> TVar.t -> Value.t -> unit) ->
    term_to_var_hooks:('st -> Term_to_var.hook list) ->
    unit ->
    builder
end

(** {2 Basics} *)

type t

val create :
  ?stats:Stat.t ->
  arg:(module ARG) ->
  Term.store ->
  TVar.store ->
  proof_tracer:Sidekick_proof.Tracer.t ->
  unit ->
  t
(** Create new core solver *)

val tst : t -> Term.store
val vst : t -> TVar.store
val trail : t -> Trail.t
val add_plugin : t -> Plugin.builder -> unit
val iter_plugins : t -> f:(Plugin.t -> unit) -> unit

val last_res : t -> Check_res.t option
(** Last result. Reset on backtracking/assertion *)

(** {2 Backtracking} *)

include Sidekick_sigs.BACKTRACKABLE0 with type t := t

(** {2 Map terms to variables} *)

val get_term_to_var : t -> Term_to_var.t
val term_to_var : t -> Term.t -> TVar.t
val add_term_to_var_hook : t -> Term_to_var.hook -> unit

(** {2 Main solving API} *)

val assign :
  t -> TVar.t -> value:Value.t -> level:int -> reason:Reason.t -> unit

val solve :
  on_exit:(unit -> unit) list ->
  on_progress:(unit -> unit) ->
  should_stop:(int -> bool) ->
  assumptions:Lit.t list ->
  t ->
  Check_res.t
