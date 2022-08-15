open Types_

(* TODO: full EGG, also have a function to update the value when
   the subterms (produced in [of_term]) are updated *)

(** Data attached to the congruence closure classes.

    This helps theories keeping track of some state for each class.
    The state of a class is the monoidal combination of the state for each
    Term.t in the class (for example, the set of terms in the
    class whose head symbol is a datatype constructor). *)
module type MONOID_PLUGIN_ARG = sig
  type t
  (** Some type with a monoid structure *)

  include Sidekick_sigs.PRINT with type t := t

  type state

  val create : CC.t -> state
  (** Initialize state from the congruence closure *)

  val name : string
  (** name of the monoid structure (short) *)

  (* FIXME: for subs, return list of e_nodes, and assume of_term already
     returned data for them. *)
  val of_term :
    CC.t -> state -> E_node.t -> Term.t -> t option * (E_node.t * t) list
  (** [of_term n t], where [t] is the Term.t annotating node [n],
      must return [maybe_m, l], where:

      - [maybe_m = Some m] if [t] has monoid value [m];
        otherwise [maybe_m=None]
      - [l] is a list of [(u, m_u)] where each [u]'s Term.t
        is a direct subterm of [t]
        and [m_u] is the monoid value attached to [u].

      *)

  val merge :
    CC.t ->
    state ->
    E_node.t ->
    t ->
    E_node.t ->
    t ->
    Expl.t ->
    (t * CC.Handler_action.t list, CC.Handler_action.conflict) result
  (** Monoidal combination of two values.

      [merge cc n1 mon1 n2 mon2 expl] returns the result of merging
      monoid values [mon1] (for class [n1]) and [mon2] (for class [n2])
      when [n1] and [n2] are merged with explanation [expl].

      @return [Ok mon] if the merge is acceptable, annotating the class of [n1 ∪ n2];
      or [Error expl'] if the merge is unsatisfiable. [expl'] can then be
      used to trigger a conflict and undo the merge.
    *)
end

(** Stateful plugin holding a per-equivalence-class monoid.

    Helps keep track of monoid state per equivalence class.
    A theory might use one or more instance(s) of this to
    aggregate some theory-specific state over all terms, with
    the information of what terms are already known to be equal
    potentially saving work for the theory. *)
module type DYN_MONOID_PLUGIN = sig
  module M : MONOID_PLUGIN_ARG
  include Sidekick_sigs.DYN_BACKTRACKABLE

  val pp : unit Fmt.printer

  val mem : E_node.t -> bool
  (** Does the CC E_node.t have a monoid value? *)

  val get : E_node.t -> M.t option
  (** Get monoid value for this CC E_node.t, if any *)

  val iter_all : (CC.repr * M.t) Iter.t
end

(** Builder for a plugin.

    The builder takes a congruence closure, and instantiate the
    plugin on it. *)
module type MONOID_PLUGIN_BUILDER = sig
  module M : MONOID_PLUGIN_ARG

  module type DYN_PL_FOR_M = DYN_MONOID_PLUGIN with module M = M

  type t = (module DYN_PL_FOR_M)

  val create_and_setup : ?size:int -> CC.t -> t
  (** Create a new monoid state *)
end
