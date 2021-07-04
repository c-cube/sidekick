(** {1 Mini congruence closure}

    This implementation is as simple as possible, and doesn't provide
    backtracking, theories, or explanations.
    It just decides the satisfiability of a set of (dis)equations.
*)

module CC_view = Sidekick_core.CC_view

(** Argument for the functor {!Make}

    It only requires a term structure, and a congruence-oriented view. *)
module type ARG = sig
  module T : Sidekick_core.TERM

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t
end

(** Main signature for an instance of the mini congruence closure *)
module type S = sig
  type term
  type fun_
  type term_store

  type t
  (** An instance of the congruence closure. Mutable *)

  val create : term_store -> t
  (** New instance *)

  val clear : t -> unit
  (** Fully reset the congruence closure's state *)

  val add_lit : t -> term -> bool -> unit
  (** [add_lit cc p sign] asserts that [p] is true if [sign],
      or [p] is false if [not sign]. If [p] is an equation and [sign]
      is [true], this adds a new equation to the congruence relation. *)

  val check_sat : t -> bool
  (** [check_sat cc] returns [true] if the current state is satisfiable, [false]
      if it's unsatisfiable. *)

  val classes : t -> term Iter.t Iter.t
  (** Traverse the set of classes in the congruence closure.
      This should be called only if {!check} returned [Sat]. *)
end

(** Instantiate the congruence closure for the given term structure. *)
module Make(A: ARG)
  : S with type term = A.T.Term.t
       and type fun_ = A.T.Fun.t
       and type term_store = A.T.Term.store
