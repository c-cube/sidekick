(** Core logic terms.

  The core terms are expressions in the calculus of constructions,
  with no universe polymorphism nor cumulativity. It should be fast, with hashconsing;
  and simple enough (no inductives, no universe trickery).

  It is intended to be the foundation for user-level terms and types and formulas.
*)

open Types_

type nonrec var = var
type nonrec bvar = bvar
type nonrec term = term

type t = term
(** A term, in the calculus of constructions *)

type store
(** The store for terms.

    The store is responsible for allocating unique IDs to terms, and
    enforcing their hashconsing (so that syntactic equality is just a pointer
    comparison). *)

(** View.

    A view is the shape of the root node of a term. *)
type view = term_view =
  | E_type of int
  | E_var of var
  | E_bound_var of bvar
  | E_const of const
  | E_app of t * t
  | E_app_fold of {
      f: term;  (** function to fold *)
      args: term list;  (** Arguments to the fold *)
      acc0: term;  (** initial accumulator *)
    }
  | E_lam of string * t * t
  | E_pi of string * t * t

include EQ_ORD_HASH with type t := t

val pp_debug : t Fmt.printer
val pp_debug_with_ids : t Fmt.printer

(** {2 Containers} *)

include WITH_SET_MAP_TBL with type t := t

(** {2 Utils} *)

val view : t -> view
val unfold_app : t -> t * t list
val is_app : t -> bool
val is_const : t -> bool

val iter_dag : ?seen:unit Tbl.t -> iter_ty:bool -> f:(t -> unit) -> t -> unit
(** [iter_dag t ~f] calls [f] once on each subterm of [t], [t] included.
        It must {b not} traverse [t] as a tree, but rather as a
        perfectly shared DAG.

        For example, in:
        {[
          let x = 2 in
          let y = f x x in
          let z = g y x in
          z = z
        ]}

        the DAG has the following nodes:

        {[ n1: 2
           n2: f n1 n1
           n3: g n2 n1
           n4: = n3 n3
         ]}
    *)

val iter_shallow : f:(bool -> t -> unit) -> t -> unit
(** [iter_shallow f e] iterates on immediate subterms of [e],
  calling [f trdb e'] for each subterm [e'], with [trdb = true] iff
  [e'] is directly under a binder. *)

val map_shallow : store -> f:(bool -> t -> t) -> t -> t
val exists_shallow : f:(bool -> t -> bool) -> t -> bool
val for_all_shallow : f:(bool -> t -> bool) -> t -> bool
val contains : t -> sub:t -> bool
val free_vars_iter : t -> var Iter.t
val free_vars : ?init:Var.Set.t -> t -> Var.Set.t

val is_type : t -> bool
(** [is_type t] is true iff [view t] is [Type _] *)

val is_a_type : t -> bool
(** [is_a_type t] is true if [is_ty (ty t)] *)

val is_closed : t -> bool
(** Is the term closed (all bound variables are paired with a binder)?
 time: O(1) *)

val has_fvars : t -> bool
(** Does the term contain free variables?
  time: O(1)  *)

val ty : t -> t
(** Return the type of this term. *)

(** {2 Creation} *)

module Store : sig
  type t = store

  val create : ?size:int -> unit -> t
  val size : t -> int
end

val type_ : store -> t
val type_of_univ : store -> int -> t
val var : store -> var -> t
val var_str : store -> string -> ty:t -> t
val bvar : store -> bvar -> t
val bvar_i : store -> int -> ty:t -> t
val const : store -> const -> t
val app : store -> t -> t -> t
val app_l : store -> t -> t list -> t
val app_fold : store -> f:t -> acc0:t -> t list -> t
val lam : store -> var -> t -> t
val pi : store -> var -> t -> t
val arrow : store -> t -> t -> t
val arrow_l : store -> t list -> t -> t
val open_lambda : store -> t -> (var * t) option
val open_lambda_exn : store -> t -> var * t

(** De bruijn indices *)
module DB : sig
  val lam_db : ?var_name:string -> store -> var_ty:t -> t -> t
  (** [lam_db store ~var_ty bod] is [\ _:var_ty. bod]. Not DB shifting is done. *)

  val pi_db : ?var_name:string -> store -> var_ty:t -> t -> t
  (** [pi_db store ~var_ty bod] is [pi _:var_ty. bod]. Not DB shifting is done. *)

  val subst_db0 : store -> t -> by:t -> t
  (** [subst_db0 store t ~by] replaces bound variable 0 in [t] with
      the term [by]. This is useful, for example, to implement beta-reduction.

      For example, with [t] being [_[0] = (\x. _[2] _[1] x[0])],
      [subst_db0 store t ~by:"hello"] is ["hello" = (\x. _[2] "hello" x[0])].
  *)

  val shift : store -> t -> by:int -> t
  (** [shift store t ~by] shifts all bound variables in [t] that are not
    closed on, by amount [by] (which must be >= 0).

    For example, with term [t] being [\x. _[1] _[2] x[0]],
    [shift store t ~by:5] is [\x. _[6] _[7] x[0]]. *)

  val abs_on : store -> var -> t -> t
  (** [abs_on store v t] is the term [t[v := _[0]]]. It replaces [v] with
      the bound variable with the same type as [v], and the DB index 0,
      and takes care of shifting if [v] occurs under binders.

      For example, [abs_on store x (\y. x+y)] is [\y. _[1] y].
  *)
end

(**/**)

module Internal_ : sig
  type cache

  val create_cache : int -> cache
  val subst_ : store -> recursive:bool -> t -> subst -> t

  val replace_ :
    ?cache:cache ->
    store ->
    recursive:bool ->
    t ->
    f:(recurse:(t -> t) -> t -> t option) ->
    t
end

(**/**)
