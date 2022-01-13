

(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LIA *)

open Sidekick_core
include module type of Intf_lia

module Make(A : ARG) : S with module A=A
