
(** Solving Linear systems of rational equations. *)

module type VAR = Linear_expr_intf.VAR
module type FRESH = Linear_expr_intf.FRESH
module type VAR_GEN = Linear_expr_intf.VAR_GEN

module type S = Simplex_intf.S
module type S_FULL = Simplex_intf.S_FULL

(** Low level simplex interface *)
module Make(V : VAR) :
  S with type var = V.t
     and type lit = V.lit
     and type param = unit
     and module Var_map = CCMap.Make(V)

(** High-level simplex interface *)
module Make_full_for_expr(V : VAR_GEN)
    (L : Linear_expr.S with type Var.t = V.t and type Var.lit = V.lit and type C.t = Q.t)
  : S_FULL with type var = V.t
            and type lit = V.lit
            and module L = L
            and module Var_map = L.Var_map
            and type L.var = V.t
            and type L.Comb.t = L.Comb.t
            and type param = V.Fresh.t

module Make_full(V : VAR_GEN)
  : S_FULL with type var = V.t
            and type lit = V.lit
            and type L.var = V.t
            and type param = V.Fresh.t
