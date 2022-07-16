(** Congruence Closure Implementation *)

module View = Sidekick_sigs_cc.View

module type TERM = Sidekick_sigs_cc.TERM
module type LIT = Sidekick_sigs_cc.LIT
module type ARG = Sidekick_sigs_cc.ARG
module type S = Sidekick_sigs_cc.S
module type MONOID_ARG = Sidekick_sigs_cc.MONOID_ARG
module type PLUGIN = Sidekick_sigs_cc.PLUGIN
module type PLUGIN_BUILDER = Sidekick_sigs_cc.PLUGIN_BUILDER

module Make (A : ARG) :
  S
    with module T = A.T
     and module Lit = A.Lit
     and module Proof_trace = A.Proof_trace

(** Create a plugin builder from the given per-class monoid *)
module Make_plugin (M : MONOID_ARG) : PLUGIN_BUILDER with module M = M
