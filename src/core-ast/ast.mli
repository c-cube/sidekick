(** Core AST.

  The core AST is composed of expressions in the calculus of constructions,
  with no universe polymorphism nor cumulativity. It should be fast, with hashconsing;
  and simple enough (no inductives, no universe trickery).

  It is intended to be the foundation for user-level terms and types and formulas.
*)

module Const = Const

(** {2 Main declarations} *)

type t
(** An AST node, i.e. an expression in the calculus of constructions *)

type term = t
type var = { v_name: string; v_ty: t }
type bvar = { bv_idx: int; bv_ty: t }

type store
(** The store for these AST nodes.

    The store is responsible for allocating unique IDs to terms, and
    enforcing their hashconsing (so that syntactic equality is just a pointer
    comparison). *)

(** View.

    A view is the shape of the root node of an AST. *)
type view =
  | E_type of int
  | E_var of var
  | E_bound_var of bvar
  | E_const of Const.t * t (* ty *)
  | E_app of t * t
  | E_lam of string * t * t
  | E_pi of string * t * t

include EQ_ORD_HASH with type t := t

val pp_debug : t Fmt.printer
val pp_debug_with_ids : t Fmt.printer

(** {2 Variables} *)

(** Free variable *)
module Var : sig
  type t = var

  include EQ_ORD_HASH_PRINT with type t := t

  val pp_with_ty : t Fmt.printer
  val make : string -> term -> t
  val makef : ('a, Format.formatter, unit, t) format4 -> term -> 'a
  val name : t -> string
  val ty : t -> term

  include WITH_SET_MAP_TBL with type t := t
end

(** Bound variable *)
module BVar : sig
  type t = bvar

  include EQ_HASH_PRINT with type t := t

  val make : int -> term -> t
  val ty : t -> term
end

(** {2 Containers} *)

include WITH_SET_MAP_TBL with type t := t

(** {2 Utils} *)

val view : t -> view
val unfold_app : t -> t * t list
val iter_dag : ?seen:unit Tbl.t -> iter_ty:bool -> f:(t -> unit) -> t -> unit

val iter_shallow : f:(bool -> t -> unit) -> t -> unit
(** [iter_shallow f e] iterates on immediate subterms of [e],
  calling [f trdb e'] for each subterm [e'], with [trdb = true] iff
  [e'] is directly under a binder. *)

val exists_shallow : f:(bool -> t -> bool) -> t -> bool
val for_all_shallow : f:(bool -> t -> bool) -> t -> bool
val contains : t -> sub:t -> bool
val free_vars_iter : t -> var Iter.t
val free_vars : ?init:Var.Set.t -> t -> Var.Set.t

val is_closed : t -> bool
(** Is the term closed (all bound variables are paired with a binder)?
 time: O(1) *)

val has_fvars : t -> bool
(** Does the term contain free variables?
  time: O(1)  *)

(** {2 Creation} *)

module Store : sig
  type t = store

  val create : unit -> t
end

val type_ : store -> t
val type_of_univ : store -> int -> t
val var : store -> var -> t
val var_str : store -> string -> ty:t -> t
val app : store -> t -> t -> t
val app_l : store -> t -> t list -> t
val lam : store -> var -> t -> t
val pi : store -> var -> t -> t
val arrow : store -> t -> t -> t
val arrow_l : store -> t list -> t -> t
val open_lambda : store -> t -> (var * t) option
val open_lambda_exn : store -> t -> var * t

val get_ty : store -> t -> t
(** [get_ty store t] gets the type of [t], or computes it on demand
    in case [t] is itself a type. *)

(** Substitutions *)
module Subst : sig
  type t

  include PRINT with type t := t

  val empty : t
  val is_empty : t -> bool
  val of_list : (var * term) list -> t
  val of_iter : (var * term) Iter.t -> t
  val to_iter : t -> (var * term) Iter.t
  val add : var -> term -> t -> t
  val apply : store -> recursive:bool -> t -> term -> term
end
