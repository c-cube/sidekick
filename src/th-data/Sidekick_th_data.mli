(** Theory for datatypes. *)

(** Datatype-oriented view of terms.

    - ['c] is the representation of constructors
    - ['t] is the representation of terms
*)
type ('c,'t) data_view =
  | T_cstor of 'c * 't IArray.t (** [T_cstor (c,args)] is the term [c(args)] *)
  | T_select of 'c * int * 't
  (** [T_select (c,i,u)] means the [i]-th argument of [u], which should
      start with constructor [c] *)
  | T_is_a of 'c * 't (** [T_is_a (c,u)] means [u] starts with constructor [c] *)
  | T_other of 't (** non-datatype term *)

(* TODO: use ['ts] rather than IArray? *)

(** View of types in a way that is directly useful for the theory of datatypes *)
type ('c, 'ty) data_ty_view =
  | Ty_arrow of 'ty Iter.t * 'ty
  | Ty_app of {
      args: 'ty Iter.t;
    }
  | Ty_data of {
      cstors: 'c;
    }
  | Ty_other

(** Argument to the functor *)
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

  val mk_cstor : S.T.Term.state -> Cstor.t -> S.T.Term.t IArray.t -> S.T.Term.t
  (** Make a constructor application term *)

  val mk_is_a: S.T.Term.state -> Cstor.t -> S.T.Term.t -> S.T.Term.t
  (** Make a [is-a] term *)

  val mk_sel : S.T.Term.state -> Cstor.t -> int -> S.T.Term.t -> S.T.Term.t
  (** Make a selector term *)

  val mk_eq : S.T.Term.state -> S.T.Term.t -> S.T.Term.t -> S.T.Term.t
  (** Make a term equality *)

  val ty_is_finite : S.T.Ty.t -> bool
  (** Is the given type known to be finite? For example a finite datatype
      (an "enum" in C parlance), or [Bool], or [Array Bool Bool]. *)

  val ty_set_is_finite : S.T.Ty.t -> bool -> unit
  (** Modify the "finite" field (see {!ty_is_finite}) *)

  (* TODO: should we store this ourself? would be simpler… *)

  val proof_isa_split : S.T.Ty.t -> S.T.Term.t Iter.t -> S.P.t
  val proof_isa_disj : S.T.Ty.t -> S.T.Term.t -> S.T.Term.t -> S.P.t
  val proof_cstor_inj : Cstor.t -> int -> S.T.Term.t list -> S.T.Term.t list -> S.P.t
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
  (** A theory that can be added to {!A.S} to perform datatype reasoning. *)
end

module Make(A : ARG) : S with module A = A
