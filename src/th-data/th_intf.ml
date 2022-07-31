open Sidekick_core
module SMT = Sidekick_smt_solver

type ty = Term.t

(** Datatype-oriented view of terms.

    - ['c] is the representation of constructors
    - ['t] is the representation of terms
*)
type ('c, 't) data_view =
  | T_cstor of 'c * 't array
  | T_select of 'c * int * 't
  | T_is_a of 'c * 't
  | T_other of 't

(** View of types in a way that is directly useful for the theory of datatypes *)
type ('c, 'ty) data_ty_view =
  | Ty_arrow of 'ty Iter.t * 'ty
  | Ty_app of { args: 'ty Iter.t }
  | Ty_data of { cstors: 'c }
  | Ty_other

module type PROOF_RULES = sig
  val lemma_isa_cstor : cstor_t:Term.t -> Term.t -> Proof_term.data
  (** [lemma_isa_cstor (d …) (is-c t)] returns the clause
      [(c …) = t |- is-c t] or [(d …) = t |- ¬ (is-c t)] *)

  val lemma_select_cstor : cstor_t:Term.t -> Term.t -> Proof_term.data
  (** [lemma_select_cstor (c t1…tn) (sel-c-i t)]
      returns a proof of [t = c t1…tn |- (sel-c-i t) = ti] *)

  val lemma_isa_split : Term.t -> Lit.t list -> Proof_term.data
  (** [lemma_isa_split t lits] is the proof of
      [is-c1 t \/ is-c2 t \/ … \/ is-c_n t] *)

  val lemma_isa_sel : Term.t -> Proof_term.data
  (** [lemma_isa_sel (is-c t)] is the proof of
      [is-c t |- t = c (sel-c-1 t)…(sel-c-n t)] *)

  val lemma_isa_disj : Lit.t -> Lit.t -> Proof_term.data
  (** [lemma_isa_disj (is-c t) (is-d t)] is the proof
      of [¬ (is-c t) \/ ¬ (is-c t)] *)

  val lemma_cstor_inj : Term.t -> Term.t -> int -> Proof_term.data
  (** [lemma_cstor_inj (c t1…tn) (c u1…un) i] is the proof of
      [c t1…tn = c u1…un |- ti = ui] *)

  val lemma_cstor_distinct : Term.t -> Term.t -> Proof_term.data
  (** [lemma_isa_distinct (c …) (d …)] is the proof
      of the unit clause [|- (c …) ≠ (d …)] *)

  val lemma_acyclicity : (Term.t * Term.t) list -> Proof_term.data
  (** [lemma_acyclicity pairs] is a proof of [t1=u1, …, tn=un |- false]
      by acyclicity. *)
end

(* TODO: remove? or make compute_card use that? *)

(** An abtract representation of a datatype *)
module type DATA_TY = sig
  type t
  type cstor

  val equal : t -> t -> bool
  val finite : t -> bool
  val set_finite : t -> bool -> unit
  val view : t -> (cstor, t) data_ty_view
  val cstor_args : cstor -> t Iter.t
end

module type ARG = sig
  (** Constructor symbols.

      A constructor is an injective symbol, part of a datatype (or "sum type").
      For example, in [type option a = Some a | None],
      the constructors are [Some] and [None]. *)
  module Cstor : sig
    type t
    (** Constructor *)

    val ty_args : t -> ty Iter.t
    (** Type arguments, for a polymorphic constructor *)

    include Sidekick_sigs.EQ with type t := t
    include Sidekick_sigs.PRINT with type t := t
  end

  val as_datatype : ty -> (Cstor.t Iter.t, ty) data_ty_view
  (** Try to view type as a datatype (with its constructors) *)

  val view_as_data : Term.t -> (Cstor.t, Term.t) data_view
  (** Try to view Term.t as a datatype Term.t *)

  val mk_cstor : Term.store -> Cstor.t -> Term.t array -> Term.t
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

  module P : PROOF_RULES
end
