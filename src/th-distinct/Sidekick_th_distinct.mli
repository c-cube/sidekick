
(** {1 Theory of "distinct"}

    This is an extension of the congruence closure that handles
    "distinct" efficiently.
  *)

module type ARG = sig
  module S : Sidekick_core.SOLVER
  val as_distinct : S.A.Term.t -> S.A.Term.t Iter.t option
  val mk_eq : S.A.Term.state -> S.A.Term.t -> S.A.Term.t -> S.A.Term.t
end
  
module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A
