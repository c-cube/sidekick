(** Main solver interface.

   This is the interface to the user, presenting SMT solver operations.
   It relies on {!Core} to implement the CDSAT calculus, and
   implements the {!Sidekick_abstract_solver} generic interface on top of it.
*)

open Sidekick_proof
module Plugin_action = Core.Plugin_action
module Plugin = Core.Plugin

module type ARG = sig
  module Core : Core.ARG
  module Bool : Plugin_bool.ARG
  module UF : Plugin_uninterpreted.ARG
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
(** Create new solver *)

val tst : t -> Term.store
val vst : t -> TVar.store
val core : t -> Core.t
val add_plugin : t -> Plugin.builder -> unit
val iter_plugins : t -> Plugin.t Iter.t

(** {2 Solving} *)

val as_asolver : t -> Sidekick_abstract_solver.t
