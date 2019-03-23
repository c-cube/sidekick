
open Solver_types

type t = term = {
  mutable term_id : int;
  mutable term_ty : ty;
  term_view : t term_view;
}

type 'a view = 'a term_view =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | Eq of 'a * 'a
  | If of 'a * 'a * 'a
  | Not of 'a

val id : t -> int
val view : t -> term view
val ty : t -> Ty.t
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

type state

val create : ?size:int -> unit -> state

val make : state -> t view -> t
val true_ : state -> t
val false_ : state -> t
val bool : state -> bool -> t
val const : state -> cst -> t
val app_cst : state -> cst -> t IArray.t -> t
val eq : state -> t -> t -> t
val if_: state -> t -> t -> t -> t
val and_eager : state -> t -> t -> t (* evaluate left argument first *)
val not_ : state -> t -> t

(** Obtain unsigned version of [t], + the sign as a boolean *)
val abs : state -> t -> t * bool

module Iter_dag : sig
  type t
  val create : unit -> t
  val iter_dag : t -> term -> term Sequence.t
end

val iter_dag : t -> t Sequence.t

val pp : t Fmt.printer

(** {6 Views} *)

val is_true : t -> bool
val is_false : t -> bool
val is_const : t -> bool

val cc_view : t -> (cst,t,t Sequence.t) Sidekick_cc.view

(* return [Some] iff the term is an undefined constant *)
val as_cst_undef : t -> (cst * Ty.Fun.t) option

(** {6 Containers} *)

module Tbl : CCHashtbl.S with type key = t
module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
