(** Plugin for uninterpreted symbols *)

open Sidekick_core

(** Argument to the plugin *)
module type ARG = sig
  val is_unin_function : Term.t -> bool
  (** [is_unin_function t] should be true iff [t] is a function symbol
    or constant symbol that is uninterpreted
    (possibly applied to {b type} arguments in the case of a polymorphic
    function/constant). *)
end

val builder : (module ARG) -> Core.Plugin.builder
(** Create a new plugin *)
