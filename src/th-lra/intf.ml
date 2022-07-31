open Sidekick_core
module SMT = Sidekick_smt_solver
module Predicate = Sidekick_simplex.Predicate
module Linear_expr = Sidekick_simplex.Linear_expr
module Linear_expr_intf = Sidekick_simplex.Linear_expr_intf

module type INT = Sidekick_arith.INT
module type RATIONAL = Sidekick_arith.RATIONAL

module S_op = Sidekick_simplex.Op

type term = Term.t
type ty = Term.t
type pred = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq
type op = Linear_expr_intf.op = Plus | Minus

type ('num, 'a) lra_view =
  | LRA_pred of pred * 'a * 'a
  | LRA_op of op * 'a * 'a
  | LRA_mult of 'num * 'a
  | LRA_const of 'num
  | LRA_other of 'a

let map_view f (l : _ lra_view) : _ lra_view =
  match l with
  | LRA_pred (p, a, b) -> LRA_pred (p, f a, f b)
  | LRA_op (p, a, b) -> LRA_op (p, f a, f b)
  | LRA_mult (n, a) -> LRA_mult (n, f a)
  | LRA_const q -> LRA_const q
  | LRA_other x -> LRA_other (f x)

module type ARG = sig
  module Z : INT
  module Q : RATIONAL with type bigint = Z.t

  val view_as_lra : Term.t -> (Q.t, Term.t) lra_view
  (** Project the Term.t into the theory view *)

  val mk_lra : Term.store -> (Q.t, Term.t) lra_view -> Term.t
  (** Make a Term.t from the given theory view *)

  val ty_lra : Term.store -> ty

  val has_ty_real : Term.t -> bool
  (** Does this term have the type [Real] *)

  val lemma_lra : Lit.t list -> Proof_term.data

  module Gensym : sig
    type t

    val create : Term.store -> t
    val tst : t -> Term.store
    val copy : t -> t

    val fresh_term : t -> pre:string -> ty -> term
    (** Make a fresh term of the given type *)
  end
end
