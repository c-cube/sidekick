
(** SMT Solver and Theories for [Sidekick_base].

    This contains instances of the SMT solver, and theories,
    from {!Sidekick_core}, using data structures from
    {!Sidekick_base}. *)

open Sidekick_base

(** Argument to the SMT solver *)
module Solver_arg = struct
  module T = Sidekick_base

  let cc_view = Term.cc_view
  let is_valid_literal _ = true
  module P = Proof
end

(** SMT solver, obtained from {!Sidekick_msat_solver} *)
module Solver = Sidekick_msat_solver.Make(Solver_arg)

(** Theory of datatypes *)
module Th_data = Sidekick_th_data.Make(struct
    module S = Solver
    open Base_types
    open Sidekick_th_data
    module Cstor = Cstor

    let as_datatype ty = match Ty.view ty with
      | Ty_atomic {def=Ty_data data;_} ->
        Ty_data {cstors=Lazy.force data.data.data_cstors |> ID.Map.values}
      | Ty_atomic {def=_;args;finite=_} ->
        Ty_app{args=Iter.of_list args}
      | Ty_bool | Ty_real -> Ty_app {args=Iter.empty}

    let view_as_data t = match Term.view t with
      | Term.App_fun ({fun_view=Fun.Fun_cstor c;_}, args) -> T_cstor (c, args)
      | Term.App_fun ({fun_view=Fun.Fun_select sel;_}, args) ->
        assert (IArray.length args=1);
        T_select (sel.select_cstor, sel.select_i, IArray.get args 0)
      | Term.App_fun ({fun_view=Fun.Fun_is_a c;_}, args) ->
        assert (IArray.length args=1);
        T_is_a (c, IArray.get args 0)
      | _ -> T_other t

    let mk_eq = Term.eq
    let mk_cstor tst c args : Term.t = Term.app_fun tst (Fun.cstor c) args
    let mk_sel tst c i u = Term.app_fun tst (Fun.select_idx c i) (IArray.singleton u)
    let mk_is_a tst c u : Term.t =
      if c.cstor_arity=0 then (
        Term.eq tst u (Term.const tst (Fun.cstor c))
      ) else (
        Term.app_fun tst (Fun.is_a c) (IArray.singleton u)
      )

    let ty_is_finite = Ty.finite
    let ty_set_is_finite = Ty.set_finite

    let proof_isa_disj = Proof.isa_disj
    let proof_isa_split = Proof.isa_split
    let proof_cstor_inj = Proof.cstor_inj
  end)

(** Reducing boolean formulas to clauses *)
module Th_bool = Sidekick_th_bool_static.Make(struct
  module S = Solver
  type term = S.T.Term.t
  include Form
  let proof_bool_eq = Proof.bool_eq
  let proof_bool_c = Proof.bool_c
  let proof_ite_true = Proof.ite_true
  let proof_ite_false = Proof.ite_false
end)

(** Theory of Linear Rational Arithmetic *)
module Th_lra = Sidekick_arith_lra.Make(struct
  module S = Solver
  module T = Term
  module Q = Sidekick_zarith.Rational
  type term = S.T.Term.t
  type ty = S.T.Ty.t

  let mk_eq = Form.eq
  let mk_lra = T.lra
  let mk_bool = T.bool
  let view_as_lra t = match T.view t with
    | T.LRA l -> l
    | T.Eq (a,b) when Ty.equal (T.ty a) (Ty.real()) -> LRA_pred (Eq, a, b)
    | _ -> LRA_other t

  let ty_lra _st = Ty.real()
  let has_ty_real t = Ty.equal (T.ty t) (Ty.real())

  let proof_lra = Proof.lra
  let proof_lra_l = Proof.lra_l

  module Gensym = struct
    type t = {
      tst: T.store;
      mutable fresh: int;
    }

    let create tst : t = {tst; fresh=0}
    let tst self = self.tst
    let copy s = {s with tst=s.tst}

    let fresh_term (self:t) ~pre (ty:Ty.t) : T.t =
      let name = Printf.sprintf "_sk_lra_%s%d" pre self.fresh in
      self.fresh <- 1 + self.fresh;
      let id = ID.make name in
      Term.const self.tst @@ Fun.mk_undef_const id ty
  end
end)

let th_bool : Solver.theory = Th_bool.theory
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
