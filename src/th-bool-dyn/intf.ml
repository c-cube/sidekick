open Sidekick_core
module SMT = Sidekick_smt_solver
module Simplify = Sidekick_simplify

type term = Term.t
type ty = Term.t

(** Boolean-oriented view of terms *)
type 'a bool_view = 'a Bool_view.t =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'a * 'a
  | B_or of 'a * 'a
  | B_imply of 'a * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_atom of 'a

(** Argument to the theory *)
module type ARG = sig
  val view_as_bool : term -> term bool_view
  (** Project the term into the boolean view. *)

  val mk_bool : Term.store -> term bool_view -> term
  (** Make a term from the given boolean view. *)
end
