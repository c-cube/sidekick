
(** {1 Mini congruence closure}

    This implementation is as simple as possible, and doesn't provide
    backtracking, theories, or explanations.
    It just decides the satisfiability of a set of (dis)equations.
*)

open Congruence_closure_intf

type res =
  | Sat
  | Unsat

module type TERM = Congruence_closure_intf.TERM

module type S = sig
  type term
  type fun_
  type term_state

  type t

  val create : term_state -> t

  val add_lit : t -> term -> bool -> unit
  (** [add_lit cc p sign] asserts that [p=sign] *)

  val distinct : t -> term list -> unit
  (** [distinct cc l] asserts that all terms in [l] are distinct *)

  val check : t -> res

  val classes : t -> term Iter.t Iter.t
  (** Traverse the set of classes in the congruence closure.
      This should be called only if {!check} returned [Sat]. *)
end

module Make(A: TERM)
  : S with type term = A.Term.t
       and type fun_ = A.Fun.t
       and type term_state = A.Term.state
