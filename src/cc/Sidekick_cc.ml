open Sidekick_core
module View = View

module type ARG = Sigs.ARG
module type S = Sigs.S
module type MONOID_PLUGIN_ARG = Sigs.MONOID_PLUGIN_ARG
module type MONOID_PLUGIN_BUILDER = Sigs.MONOID_PLUGIN_BUILDER

module Make (A : ARG) : S = Core_cc.Make (A)
