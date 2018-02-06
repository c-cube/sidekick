
open Solver_types

type t = term

val id : t -> int
val cell : t -> term term_cell
val ty : t -> Ty.t
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

type state

val create : ?size:int -> unit -> state

val true_ : state -> t
val false_ : state -> t
val const : state -> cst -> t
val app_cst : state -> cst -> t IArray.t -> t
val if_: state -> t -> t -> t -> t
val case : state -> t -> t ID.Map.t -> t
val builtin : state -> t builtin -> t
val and_ : state -> t -> t -> t
val or_ : state -> t -> t -> t
val not_ : state -> t -> t
val imply : state -> t list -> t -> t
val eq : state -> t -> t -> t
val neq : state -> t -> t -> t
val and_eager : state -> t -> t -> t (* evaluate left argument first *)

val cstor_test : state -> data_cstor -> term -> t
val cstor_proj : state -> data_cstor -> int -> term -> t

val and_l : state -> t list -> t
val or_l : state -> t list -> t

val abs : t -> t * bool

val map_builtin : (t -> t) -> t builtin -> t builtin
val builtin_to_seq : t builtin -> t Sequence.t

val to_seq : t -> t Sequence.t

val all_terms : state -> t Sequence.t

val pp : t Fmt.printer

(** {6 Views} *)

val is_true : t -> bool
val is_false : t -> bool
val is_const : t -> bool
val is_custom : t -> bool

val is_semantic : t -> bool
(** Custom term that is Shostak-ready (ie can be solved) *)

(* return [Some] iff the term is an undefined constant *)
val as_cst_undef : t -> (cst * Ty.t) option

val as_cstor_app : t -> (cst * data_cstor * t IArray.t) option

(* typical view for unification/equality *)
type unif_form =
  | Unif_cst of cst * Ty.t
  | Unif_cstor of cst * data_cstor * term IArray.t
  | Unif_none

val as_unif : t -> unif_form

(** {6 Containers} *)

module Tbl : CCHashtbl.S with type key = t
module Map : CCMap.S with type key = t

(**/**)
val dummy : t
(**/**)
