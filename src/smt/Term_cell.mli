
open Solver_types

type 'a cell = 'a Solver_types.term_cell =
  | Bool of bool
  | App_cst of cst * 'a IArray.t
  | If of 'a * 'a * 'a
  | Case of 'a * 'a ID.Map.t
  | Custom of {
      view : 'a term_view_custom;
      tc : term_view_tc;
    }

type 'a custom = 'a Solver_types.term_view_custom = ..

type tc = Solver_types.term_view_tc = {
  tc_t_pp : 'a. 'a Fmt.printer -> 'a term_view_custom Fmt.printer;
  tc_t_equal : 'a. 'a CCEqual.t -> 'a term_view_custom CCEqual.t;
  tc_t_hash : 'a. 'a Hash.t -> 'a term_view_custom Hash.t;
  tc_t_ty : 'a. ('a -> ty) -> 'a term_view_custom -> ty;
  tc_t_is_semantic : 'a. 'a term_view_custom -> bool;
  tc_t_solve : cc_node term_view_custom -> cc_node term_view_custom -> solve_result;
  tc_t_sub : 'a. 'a term_view_custom -> 'a Sequence.t;
  tc_t_abs : 'a. self:'a -> 'a custom -> 'a * bool;
  tc_t_relevant : 'a. 'a term_view_custom -> 'a Sequence.t;
  tc_t_subst :
    'a 'b. ('a -> 'b) -> 'a term_view_custom -> 'b term_view_custom option;
  tc_t_explain : 'a. 'a CCEqual.t -> 'a term_view_custom -> 'a term_view_custom -> ('a * 'a) list;
}


type t = term term_cell

val equal : t -> t -> bool
val hash : t -> int

val true_ : t
val false_ : t
val const : cst -> t
val app_cst : cst -> term IArray.t -> t
val cstor_test : data_cstor -> term -> t
val cstor_proj : data_cstor -> int -> term -> t
val case : term -> term ID.Map.t -> t
val if_ : term -> term -> term -> t
val custom : tc:term_view_tc -> term term_view_custom -> t

val ty : t -> Ty.t
(** Compute the type of this term cell. Not totally free *)

module Tbl : CCHashtbl.S with type key = t

module type ARG = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module Make_eq(X : ARG) : sig
  val equal : X.t term_cell -> X.t term_cell -> bool
  val hash : X.t term_cell -> int
end
