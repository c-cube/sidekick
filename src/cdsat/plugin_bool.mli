(** Plugin for boolean formulas *)

open Sidekick_core

type 'a view = 'a Bool_view.t

(** Argument to the plugin *)
module type ARG = sig
  val view : Term.t -> Term.t view
  val or_l : Term.store -> Term.t list -> Term.t
  val and_l : Term.store -> Term.t list -> Term.t
end

val builder : (module ARG) -> Core.Plugin.builder
(** Create a new plugin *)
