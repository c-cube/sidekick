(** {1 Mini congruence closure}

    This implementation is as simple as possible, and doesn't provide
    backtracking, theories, or explanations.
    It just decides the satisfiability of a set of (dis)equations.
*)

module CC_view = Sidekick_core.CC_view

module type ARG = sig
  module T : Sidekick_core.TERM

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t
end

module type S = sig
  type term
  type fun_
  type term_state

  type t

  val create : term_state -> t

  val clear : t -> unit
  (** Fully reset the congruence closure's state *)

  val add_lit : t -> term -> bool -> unit
  (** [add_lit cc p sign] asserts that [p=sign] *)

  val check_sat : t -> bool
  (** [check_sat cc] returns [true] if the current state is satisfiable, [false]
      if it's unsatisfiable *)

  val classes : t -> term Iter.t Iter.t
  (** Traverse the set of classes in the congruence closure.
      This should be called only if {!check} returned [Sat]. *)
end

module Make(A: ARG)
  : S with type term = A.T.Term.t
       and type fun_ = A.T.Fun.t
       and type term_state = A.T.Term.state
