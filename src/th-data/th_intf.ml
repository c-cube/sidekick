(** Datatype-oriented view of terms.

    - ['c] is the representation of constructors
    - ['t] is the representation of terms
*)
type ('c, 't) data_view =
  | T_cstor of 'c * 't IArray.t
  | T_select of 'c * int * 't
  | T_is_a of 'c * 't
  | T_other of 't

(** View of types in a way that is directly useful for the theory of datatypes *)
type ('c, 'ty) data_ty_view =
  | Ty_arrow of 'ty Iter.t * 'ty
  | Ty_app of { args: 'ty Iter.t }
  | Ty_data of { cstors: 'c }
  | Ty_other

module type PROOF = sig
  type term
  type lit
  type proof_step
  type proof

  val lemma_isa_cstor : cstor_t:term -> term -> proof -> proof_step
  (** [lemma_isa_cstor (d …) (is-c t)] returns the clause
      [(c …) = t |- is-c t] or [(d …) = t |- ¬ (is-c t)] *)

  val lemma_select_cstor : cstor_t:term -> term -> proof -> proof_step
  (** [lemma_select_cstor (c t1…tn) (sel-c-i t)]
      returns a proof of [t = c t1…tn |- (sel-c-i t) = ti] *)

  val lemma_isa_split : term -> lit Iter.t -> proof -> proof_step
  (** [lemma_isa_split t lits] is the proof of
      [is-c1 t \/ is-c2 t \/ … \/ is-c_n t] *)

  val lemma_isa_sel : term -> proof -> proof_step
  (** [lemma_isa_sel (is-c t)] is the proof of
      [is-c t |- t = c (sel-c-1 t)…(sel-c-n t)] *)

  val lemma_isa_disj : lit -> lit -> proof -> proof_step
  (** [lemma_isa_disj (is-c t) (is-d t)] is the proof
      of [¬ (is-c t) \/ ¬ (is-c t)] *)

  val lemma_cstor_inj : term -> term -> int -> proof -> proof_step
  (** [lemma_cstor_inj (c t1…tn) (c u1…un) i] is the proof of
      [c t1…tn = c u1…un |- ti = ui] *)

  val lemma_cstor_distinct : term -> term -> proof -> proof_step
  (** [lemma_isa_distinct (c …) (d …)] is the proof
      of the unit clause [|- (c …) ≠ (d …)] *)

  val lemma_acyclicity : (term * term) Iter.t -> proof -> proof_step
  (** [lemma_acyclicity pairs] is a proof of [t1=u1, …, tn=un |- false]
      by acyclicity. *)
end

module type ARG = sig
  module S : Sidekick_core.SOLVER

  (** Constructor symbols.

      A constructor is an injective symbol, part of a datatype (or "sum type").
      For example, in [type option a = Some a | None],
      the constructors are [Some] and [None]. *)
  module Cstor : sig
    type t
    (** Constructor *)

    val ty_args : t -> S.T.Ty.t Iter.t
    (** Type arguments, for a polymorphic constructor *)

    val pp : t Fmt.printer

    val equal : t -> t -> bool
    (** Comparison *)
  end

  val as_datatype : S.T.Ty.t -> (Cstor.t Iter.t, S.T.Ty.t) data_ty_view
  (** Try to view type as a datatype (with its constructors) *)

  val view_as_data : S.T.Term.t -> (Cstor.t, S.T.Term.t) data_view
  (** Try to view term as a datatype term *)

  val mk_cstor : S.T.Term.store -> Cstor.t -> S.T.Term.t IArray.t -> S.T.Term.t
  (** Make a constructor application term *)

  val mk_is_a : S.T.Term.store -> Cstor.t -> S.T.Term.t -> S.T.Term.t
  (** Make a [is-a] term *)

  val mk_sel : S.T.Term.store -> Cstor.t -> int -> S.T.Term.t -> S.T.Term.t
  (** Make a selector term *)

  val mk_eq : S.T.Term.store -> S.T.Term.t -> S.T.Term.t -> S.T.Term.t
  (** Make a term equality *)

  val ty_is_finite : S.T.Ty.t -> bool
  (** Is the given type known to be finite? For example a finite datatype
      (an "enum" in C parlance), or [Bool], or [Array Bool Bool]. *)

  val ty_set_is_finite : S.T.Ty.t -> bool -> unit
  (** Modify the "finite" field (see {!ty_is_finite}) *)

  module P :
    PROOF
      with type proof := S.P.t
       and type proof_step := S.P.proof_step
       and type term := S.T.Term.t
       and type lit := S.Lit.t
end
