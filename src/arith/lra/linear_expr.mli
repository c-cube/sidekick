(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

(** Arithmetic expressions *)

module type COEFF = Linear_expr_intf.COEFF

module type VAR = Linear_expr_intf.VAR

module type S = Linear_expr_intf.S

type nonrec bool_op = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq

module Make(C : COEFF)(Var : VAR)
  : S with module C = C
       and module Var = Var
       and module Var_map = CCMap.Make(Var)
