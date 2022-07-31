(** Linear Rational Arithmetic *)

module Intf = Intf
open Intf

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
