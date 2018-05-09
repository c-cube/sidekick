
open Solver_types

type t = term = {
  mutable term_id : int;
  mutable term_ty : ty;
  term_cell : t term_cell;
}

type 'a cell = 'a term_cell =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | If of 'a * 'a * 'a
  | Case of 'a * 'a ID.Map.t
  | Custom of { view : 'a term_view_custom; tc : term_view_tc; }

type 'a custom = 'a Solver_types.term_view_custom = ..

type tc = Solver_types.term_view_tc = {
  tc_t_pp : 'a. 'a Fmt.printer -> 'a custom Fmt.printer;
  tc_t_equal : 'a. 'a CCEqual.t -> 'a custom CCEqual.t;
  tc_t_hash : 'a. 'a Hash.t -> 'a custom Hash.t;
  tc_t_ty : 'a. ('a -> ty) -> 'a custom -> ty;
  tc_t_is_semantic : 'a. 'a custom -> bool;
  tc_t_solve : cc_node custom -> cc_node custom -> solve_result;
  tc_t_sub : 'a. 'a custom -> 'a Sequence.t;
  tc_t_abs : self:term -> term custom -> term * bool;
  tc_t_relevant : 'a. 'a custom -> 'a Sequence.t;
  tc_t_subst : 'a 'b. ('a -> 'b) -> 'a custom -> 'b custom option;
  tc_t_explain : 'a. 'a CCEqual.t -> 'a custom -> 'a custom -> ('a * 'a) list;
}

val id : t -> int
val cell : t -> term term_cell
val ty : t -> Ty.t
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

type state

val create : ?size:int -> unit -> state

val make : state -> t term_cell -> t
val true_ : state -> t
val false_ : state -> t
val const : state -> cst -> t
val app_cst : state -> cst -> t IArray.t -> t
val if_: state -> t -> t -> t -> t
val case : state -> t -> t ID.Map.t -> t
val and_eager : state -> t -> t -> t (* evaluate left argument first *)
val custom : state -> tc:tc -> t custom -> t

val cstor_test : state -> data_cstor -> term -> t
val cstor_proj : state -> data_cstor -> int -> term -> t

(* TODO: remove *)
val abs : t -> t * bool

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
