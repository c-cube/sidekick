(** Congruence Closure Implementation *)

open Sidekick_sigs_cc

module type EXTENDED_PLUGIN_BUILDER = sig
  include MONOID_PLUGIN_BUILDER

  val mem : t -> M.CC.E_node.t -> bool
  (** Does the CC.E_node.t have a monoid value? *)

  val get : t -> M.CC.E_node.t -> M.t option
  (** Get monoid value for this CC.E_node.t, if any *)

  val iter_all : t -> (M.CC.repr * M.t) Iter.t

  include Sidekick_sigs.BACKTRACKABLE0 with type t := t
  include Sidekick_sigs.PRINT with type t := t
end

(** Create a plugin builder from the given per-class monoid *)
module Make (M : MONOID_PLUGIN_ARG) : EXTENDED_PLUGIN_BUILDER with module M = M
