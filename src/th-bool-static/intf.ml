open Sidekick_core
module SMT = Sidekick_smt_solver
module Simplify = Sidekick_simplify

type term = Term.t
type ty = Term.t

(** Boolean-oriented view of terms *)
type ('a, 'args) bool_view =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'args
  | B_or of 'args
  | B_imply of 'args * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_opaque_bool of 'a (* do not enter *)
  | B_atom of 'a

module type PROOF_RULES = sig
  val lemma_bool_tauto : Lit.t Iter.t -> Proof_term.t
  (** Boolean tautology lemma (clause) *)

  val lemma_bool_c : string -> term list -> Proof_term.t
  (** Basic boolean logic lemma for a clause [|- c].
      [proof_bool_c b name cs] is the Proof_term.t designated by [name]. *)

  val lemma_bool_equiv : term -> term -> Proof_term.t
  (** Boolean tautology lemma (equivalence) *)

  val lemma_ite_true : ite:term -> Proof_term.t
  (** lemma [a ==> ite a b c = b] *)

  val lemma_ite_false : ite:term -> Proof_term.t
  (** lemma [¬a ==> ite a b c = c] *)
end

(** Argument to the theory *)
module type ARG = sig
  val view_as_bool : term -> (term, term Iter.t) bool_view
  (** Project the term into the boolean view. *)

  val mk_bool : Term.store -> (term, term array) bool_view -> term
  (** Make a term from the given boolean view. *)

  module P : PROOF_RULES

  (** Fresh symbol generator.

      The theory needs to be able to create new terms with fresh names,
      to be used as placeholders for complex formulas during Tseitin
      encoding. *)
  module Gensym : sig
    type t

    val create : Term.store -> t
    (** New (stateful) generator instance. *)

    val fresh_term : t -> pre:string -> ty -> term
    (** Make a fresh term of the given type *)
  end
end
