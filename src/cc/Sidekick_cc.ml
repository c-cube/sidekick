open Sidekick_core
module View = CC_view
module E_node = E_node
module Expl = Expl
module Signature = Signature
module Resolved_expl = Resolved_expl
module Plugin = Plugin
module CC = CC

module type DYN_MONOID_PLUGIN = Sigs_plugin.DYN_MONOID_PLUGIN
module type MONOID_PLUGIN_ARG = Sigs_plugin.MONOID_PLUGIN_ARG
module type MONOID_PLUGIN_BUILDER = Sigs_plugin.MONOID_PLUGIN_BUILDER

include CC
