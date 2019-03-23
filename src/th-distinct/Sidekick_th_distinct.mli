
(** {1 Theory of "distinct"}

    This is an extension of the congruence closure that handles
    "distinct" efficiently.
  *)

module Term = Sidekick_smt.Term

module type ARG = sig
  module T : sig
    type t
    type state
    val pp : t Fmt.printer
    val equal : t -> t -> bool
    val hash : t -> int
    val as_distinct : t -> t Iter.t option
    val mk_eq : state -> t -> t -> t
  end
  module Lit : sig
    type t
    val term : t -> T.t
    val neg : t -> t
    val sign : t -> bool
    val compare : t -> t -> int
    val atom : T.state -> ?sign:bool -> T.t -> t
    val pp : t Fmt.printer
  end
end
  
module type S = sig
  type term
  type term_state
  type lit

  type data
  val key : (term, lit, data) Sidekick_cc.Key.t
  val th : Sidekick_smt.Theory.t
end

(* TODO: generalize theories *)
module Make(A : ARG with type T.t = Sidekick_smt.Term.t
              and type T.state = Sidekick_smt.Term.state
              and type Lit.t = Sidekick_smt.Lit.t) :
  S with type term = A.T.t
     and type lit = A.Lit.t
     and type term_state = A.T.state

val distinct : Term.state -> Term.t IArray.t -> Term.t
val distinct_l : Term.state -> Term.t list -> Term.t

(** Default instance *)
include S with type term = Term.t and type lit = Sidekick_smt.Lit.t
