(** Linear Rational Arithmetic *)

open Sidekick_core
module Intf = Intf
module Predicate = Intf.Predicate
module SMT = Sidekick_smt_solver

module type INT = Intf.INT
module type RATIONAL = Intf.RATIONAL

module S_op = Sidekick_simplex.Op

type term = Term.t
type ty = Term.t
type pred = Intf.pred = Leq | Geq | Lt | Gt | Eq | Neq
type op = Intf.op = Plus | Minus

type ('num, 'a) lra_view = ('num, 'a) Intf.lra_view =
  | LRA_pred of pred * 'a * 'a
  | LRA_op of op * 'a * 'a
  | LRA_mult of 'num * 'a
  | LRA_const of 'num
  | LRA_other of 'a

val map_view : ('a -> 'b) -> ('c, 'a) lra_view -> ('c, 'b) lra_view

module type ARG = Intf.ARG

(* TODO
   type state

   val k_state : state SMT.Registry.key
   (** Key to access the state from outside,
         available when the theory has been setup *)

   val create : (module ARG) -> ?stat:Stat.t -> SMT.Solver_internal.t -> state

   (* TODO: be able to declare some variables as ints *)

   (*
     val simplex : state -> Simplex.t
        *)

   val theory_of_state : state -> SMT.Theory.t
*)

val theory : (module ARG) -> SMT.Theory.t
