(** Congruence Closure Implementation *)

open Sidekick_core
module View = View

module type ARG = Sigs.ARG
module type S = Sigs.S
module type DYN_MONOID_PLUGIN = Sigs.DYN_MONOID_PLUGIN
module type MONOID_PLUGIN_ARG = Sigs.MONOID_PLUGIN_ARG
module type MONOID_PLUGIN_BUILDER = Sigs.MONOID_PLUGIN_BUILDER

module Make (_ : ARG) : S

module Base : S
(** Basic implementation following terms' shape *)
