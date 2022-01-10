
open Sidekick_core

module type RATIONAL = Sidekick_arith.RATIONAL
module type INT = Sidekick_arith.INT

module S_op = Sidekick_arith_lra.S_op
type pred = Sidekick_arith_lra.pred = Leq | Geq | Lt | Gt | Eq | Neq
type op = Sidekick_arith_lra.op = Plus | Minus

type ('num, 'a) lia_view =
  | LIA_pred of pred * 'a * 'a
  | LIA_op of op * 'a * 'a
  | LIA_mult of 'num * 'a
  | LIA_const of 'num
  | LIA_simplex_var of 'a (* an opaque variable *)
  | LIA_simplex_pred of 'a * S_op.t * 'num (* an atomic constraint *)
  | LIA_other of 'a

let map_view f (l:_ lia_view) : _ lia_view =
  begin match l with
    | LIA_pred (p, a, b) -> LIA_pred (p, f a, f b)
    | LIA_op (p, a, b) -> LIA_op (p, f a, f b)
    | LIA_mult (n,a) -> LIA_mult (n, f a)
    | LIA_const q -> LIA_const q
    | LIA_simplex_var v -> LIA_simplex_var (f v)
    | LIA_simplex_pred (v, op, q) -> LIA_simplex_pred (f v, op, q)
    | LIA_other x -> LIA_other (f x)
  end

module type ARG = sig
  module S : Sidekick_core.SOLVER

  module Q : RATIONAL
  module Z : INT

  module LRA : Sidekick_arith_lra.S

  type term = S.T.Term.t
  type ty = S.T.Ty.t

  val view_as_lia : term -> (Z.t, term) lia_view
  (** Project the term into the theory view *)

  val mk_bool : S.T.Term.store -> bool -> term

  val mk_to_real : S.T.Term.store -> term -> term
  (** Wrap term into a [to_real] projector to rationals *)

  val mk_lia : S.T.Term.store -> (Z.t, term) lia_view -> term
  (** Make a term from the given theory view *)

  val ty_int : S.T.Term.store -> ty

  val mk_eq : S.T.Term.store -> term -> term -> term
  (** syntactic equality *)

  val has_ty_int : term -> bool
  (** Does this term have the type [Int] *)

  val lemma_lia : S.Lit.t Iter.t -> S.P.proof_rule
end

module type S = sig
  module A : ARG

  val theory : A.S.theory
end
