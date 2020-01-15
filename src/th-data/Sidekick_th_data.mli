
(** Datatype-oriented view of terms.
    ['c] is the representation of constructors
    ['t] is the representation of terms
*)
type ('c,'t) data_view =
  | T_cstor of 'c * 't IArray.t
  | T_select of 'c * int * 't
  | T_is_a of 'c * 't
  | T_other of 't

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

module type ARG = sig
  module S : Sidekick_core.SOLVER

  module Cstor : sig
    type t
    val ty_args : t -> S.T.Ty.t Iter.t
    val pp : t Fmt.printer
    val equal : t -> t -> bool
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

  val ty_is_finite : S.T.Ty.t -> bool
  (** Is the given type known to be finite? *)

  val ty_set_is_finite : S.T.Ty.t -> bool -> unit
  (** Modify the "finite" field (see {!ty_is_finite}) *)
end

module type S = sig
  module A : ARG
  val theory : A.S.theory
end

module Make(A : ARG) : S with module A = A
