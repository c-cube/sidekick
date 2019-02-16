
(** {1 Dynamic Tseitin conversion}

    This theory performs the conversion of boolean terms into clauses, on
    the fly, during the proof search. It is a true CDCL(T)-style theory.
    *)

module type ARG = Bool_intf.BOOL_TERM
  with type t = Sidekick_smt.Term.t
   and type state = Sidekick_smt.Term.state

module Make(Term : ARG) : sig
  type term = Term.t

  module Lit : sig
    type t = Sidekick_smt.Lit.t
    val eq : Term.state -> term -> term -> t
    val neq : Term.state -> term -> term -> t
  end

  val th : Sidekick_smt.Theory.t
end
