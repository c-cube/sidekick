(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

(** Arithmetic expressions *)

module type COEFF = Linear_expr_intf.COEFF

module type VAR = Linear_expr_intf.VAR
module type FRESH = Linear_expr_intf.FRESH
module type VAR_GEN = Linear_expr_intf.VAR_GEN
module type VAR_EXTENDED = Linear_expr_intf.VAR_EXTENDED

module type S = Linear_expr_intf.S

type nonrec bool_op = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq

module Make(C : COEFF)(Var : VAR)
  : S with module C = C
       and module Var = Var
       and module Var_map = CCMap.Make(Var)

module Make_var_gen(Var : VAR)
  : VAR_EXTENDED
    with type user_var = Var.t
     and type lit = Var.lit
