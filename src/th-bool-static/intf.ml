open Sidekick_core
module SMT = Sidekick_smt_solver
module Simplify = Sidekick_simplify

type term = Term.t
type ty = Term.t

(** Boolean-oriented view of terms *)
type ('a, 'args) bool_view = ('a, 'args) Bool_view.t =
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
  | B_atom of 'a

(** Argument to the theory *)
module type ARG = sig
  val view_as_bool : term -> (term, term list) bool_view
  (** Project the term into the boolean view. *)

  val mk_bool : Term.store -> (term, term list) bool_view -> term
  (** Make a term from the given boolean view. *)
end
