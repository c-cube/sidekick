(** Core logic terms.

  The core terms are expressions in the calculus of constructions,
  with no universe polymorphism nor cumulativity. It should be fast, with hashconsing;
  and simple enough (no inductives, no universe trickery).

  It is intended to be the foundation for user-level terms and types and formulas.
*)

open Types_

type bvar = Bvar.t
type nonrec term = term

type t = term
(** A term, in the calculus of constructions *)

(** View.

    A view is the shape of the root node of a term. *)
type view = term_view =
  | E_type of level
  | E_bound_var of bvar
  | E_const of const
  | E_app of t * t
  | E_lam of t * t
  | E_pi of t * t

val pp_debug : t Fmt.printer

(** {2 Utils} *)

val view : t -> view
val unfold_app : t -> t * t list
val is_app : t -> bool
val is_const : t -> bool
val is_pi : t -> bool
val as_type : t -> Level.t option
val as_type_exn : t -> Level.t

val iter_shallow : f:(bool -> t -> unit) -> t -> unit
(** [iter_shallow f e] iterates on immediate subterms of [e],
    calling [f trdb e'] for each subterm [e'], with [trdb = true] iff
    [e'] is directly under a binder. *)

val map_shallow : f:(bool -> t -> t) -> t -> t
val exists_shallow : f:(bool -> t -> bool) -> t -> bool
val for_all_shallow : f:(bool -> t -> bool) -> t -> bool

val is_type : t -> bool
(** [is_type t] is true iff [view t] is [Type _] *)

val is_closed : t -> bool
(** Is the term closed (all bound variables are paired with a binder)?
 time: O(1) *)

(** {2 Creation} *)

val type_ : t
val type_of_univ : level -> t
val type_of_univ_int : int -> t
val bvar : bvar -> t
val bvar_i : int -> t
val const : const -> t
val app : t -> t -> t
val app_l : t -> t list -> t
val lam : var_ty:t -> t -> t
val pi : var_ty:t -> t -> t

(** De bruijn indices *)
module DB : sig
  val subst_db0 : t -> by:t -> t
  (** [subst_db0 store t ~by] replaces bound variable 0 in [t] with
      the term [by]. This is useful, for example, to implement beta-reduction.

      For example, with [t] being [_[0] = (\x. _[2] _[1] x[0])],
      [subst_db0 store t ~by:"hello"] is ["hello" = (\x. _[2] "hello" x[0])].
  *)

  val shift : t -> by:int -> t
  (** [shift t ~by] shifts all bound variables in [t] that are not
      closed on, by amount [by] (which must be >= 0).

      For example, with term [t] being [\x. _[1] _[2] x[0]],
      [shift t ~by:5] is [\x. _[6] _[7] x[0]]. *)
end
