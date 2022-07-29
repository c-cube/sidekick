(** Mini congruence closure

    This implementation is as simple as possible, and doesn't provide
    backtracking, theories, or explanations.
    It just decides the satisfiability of a set of (dis)equations.
*)

open Sidekick_core
module CC_view = Sidekick_cc.View

(** Argument for the functor {!Make}

    It only requires a Term.t structure, and a congruence-oriented view. *)
module type ARG = sig
  val view_as_cc : Term.t -> (Const.t, Term.t, Term.t Iter.t) CC_view.t
end

(** Main signature for an instance of the mini congruence closure *)
module type S = sig
  type t
  (** An instance of the congruence closure. Mutable *)

  val create : Term.store -> t
  (** New instance *)

  val clear : t -> unit
  (** Fully reset the congruence closure's state *)

  val add_lit : t -> Term.t -> bool -> unit
  (** [add_lit cc p sign] asserts that [p] is true if [sign],
      or [p] is false if [not sign]. If [p] is an equation and [sign]
      is [true], this adds a new equation to the congruence relation. *)

  val check_sat : t -> bool
  (** [check_sat cc] returns [true] if the current state is satisfiable, [false]
      if it's unsatisfiable. *)

  val classes : t -> Term.t Iter.t Iter.t
  (** Traverse the set of classes in the congruence closure.
      This should be called only if {!check} returned [Sat]. *)
end

(** Instantiate the congruence closure for the given Term.t structure. *)
module Make (_ : ARG) : S
