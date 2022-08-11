open Sidekick_core
module SMT = Sidekick_smt_solver

type ty = Term.t

(** Datatype-oriented view of terms.

    - ['c] is the representation of constructors
    - ['t] is the representation of terms
*)
type ('c, 't) data_view =
  | T_cstor of 'c * 't list
  | T_select of 'c * int * 't
  | T_is_a of 'c * 't
  | T_other of 't

(** View of types in a way that is directly useful for the theory of datatypes *)
type ('c, 'ty) data_ty_view =
  | Ty_arrow of 'ty list * 'ty
  | Ty_data of { cstors: 'c }
  | Ty_other of { sub: 'ty list }

(* TODO: remove? or make compute_card use that? *)

(** An abtract representation of a datatype *)
module type DATA_TY = sig
  type t
  type cstor

  val equal : t -> t -> bool
  val finite : t -> bool
  val set_finite : t -> bool -> unit
  val view : t -> (cstor, t) data_ty_view
  val cstor_args : cstor -> t list
end

module type ARG = sig
  (** Constructor symbols.

      A constructor is an injective symbol, part of a datatype (or "sum type").
      For example, in [type option a = Some a | None],
      the constructors are [Some] and [None]. *)
  module Cstor : sig
    type t
    (** Constructor *)

    val ty_args : t -> ty list
    (** Type arguments, for a polymorphic constructor *)

    include Sidekick_sigs.EQ with type t := t
    include Sidekick_sigs.PRINT with type t := t
  end

  val as_datatype : ty -> (Cstor.t list, ty) data_ty_view
  (** Try to view type as a datatype (with its constructors) *)

  val view_as_data : Term.t -> (Cstor.t, Term.t) data_view
  (** Try to view Term.t as a datatype Term.t *)

  val mk_cstor : Term.store -> Cstor.t -> Term.t list -> Term.t
  (** Make a constructor application Term.t *)

  val mk_is_a : Term.store -> Cstor.t -> Term.t -> Term.t
  (** Make a [is-a] Term.t *)

  val mk_sel : Term.store -> Cstor.t -> int -> Term.t -> Term.t
  (** Make a selector Term.t *)

  val mk_eq : Term.store -> Term.t -> Term.t -> Term.t
  (** Make a Term.t equality *)

  val ty_is_finite : ty -> bool
  (** Is the given type known to be finite? For example a finite datatype
      (an "enum" in C parlance), or [Bool], or [Array Bool Bool]. *)

  val ty_set_is_finite : ty -> bool -> unit
  (** Modify the "finite" field (see {!ty_is_finite}) *)
end
