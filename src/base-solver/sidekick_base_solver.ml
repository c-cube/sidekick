
(** SMT Solver and Theories for [Sidekick_base].

    This contains instances of the SMT solver, and theories,
    from {!Sidekick_core}, using data structures from
    {!Sidekick_base}. *)

open! Sidekick_base

(** Argument to the SMT solver *)
module Solver_arg = struct
  module T = Sidekick_base.Solver_arg
  module Lit = Sidekick_base.Lit

  let cc_view = Term.cc_view
  let mk_eq = Term.eq
  let is_valid_literal _ = true
  module P = Sidekick_base.Proof
  type proof = P.t
  type proof_step = P.proof_step
end

(** SMT solver, obtained from {!Sidekick_smt_solver} *)
module Solver = Sidekick_smt_solver.Make(Solver_arg)

(** Theory of datatypes *)
module Th_data = Sidekick_th_data.Make(struct
    module S = Solver
    open! Base_types
    open! Sidekick_th_data
    module Proof = Proof
    module Cstor = Cstor

    let as_datatype ty = match Ty.view ty with
      | Ty_atomic {def=Ty_data data;_} ->
        Ty_data {cstors=Lazy.force data.data.data_cstors |> ID.Map.values}
      | Ty_atomic {def=_;args;finite=_} ->
        Ty_app{args=Iter.of_list args}
      | Ty_bool | Ty_real | Ty_int -> Ty_app {args=Iter.empty}

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

    module P = Proof
  end)

(** Reducing boolean formulas to clauses *)
module Th_bool = Sidekick_th_bool_static.Make(struct
  module S = Solver
  type term = S.T.Term.t
  include Form
  let lemma_bool_tauto = Proof.lemma_bool_tauto
  let lemma_bool_c = Proof.lemma_bool_c
  let lemma_bool_equiv = Proof.lemma_bool_equiv
  let lemma_ite_true = Proof.lemma_ite_true
  let lemma_ite_false = Proof.lemma_ite_false
end)

(** Theory of Linear Rational Arithmetic *)
module Th_lra = Sidekick_arith_lra.Make(struct
  module S = Solver
  module T = Term
  module Q = Sidekick_zarith.Rational
  type term = S.T.Term.t
  type ty = S.T.Ty.t

  module LRA = Sidekick_arith_lra

  let mk_eq = Form.eq
  let mk_lra store l = match l with
    | LRA.LRA_other x -> x
    | LRA.LRA_pred (p, x, y) -> T.lra store (Arith_pred(p,x,y))
    | LRA.LRA_op (op, x, y) -> T.lra store (Arith_op(op,x,y))
    | LRA.LRA_const c -> T.lra store (Arith_const c)
    | LRA.LRA_mult (c,x) -> T.lra store (Arith_mult (c,x))
    | LRA.LRA_simplex_var x -> T.lra store (Arith_simplex_var x)
    | LRA.LRA_simplex_pred (x,p,c) -> T.lra store (Arith_simplex_pred (x,p,c))
  let mk_bool = T.bool

  let rec view_as_lra t = match T.view t with
    | T.LRA l ->
      let open Base_types in
      let module LRA = Sidekick_arith_lra in
      begin match l with
        | Arith_const c -> LRA.LRA_const c
        | Arith_pred (p,a,b) -> LRA.LRA_pred(p,a,b)
        | Arith_op(op,a,b) -> LRA.LRA_op(op,a,b)
        | Arith_mult (c,x) -> LRA.LRA_mult (c,x)
        | Arith_simplex_var x -> LRA.LRA_simplex_var x
        | Arith_simplex_pred (x,p,c) -> LRA.LRA_simplex_pred(x,p,c)
        | Arith_to_real x -> view_as_lra x
        | Arith_var x -> LRA.LRA_other x
      end
    | T.Eq (a,b) when Ty.equal (T.ty a) (Ty.real()) ->
      LRA.LRA_pred (Eq, a, b)
    | _ -> LRA.LRA_other t

  let ty_lra _st = Ty.real()
  let has_ty_real t = Ty.equal (T.ty t) (Ty.real())

  let lemma_lra = Proof.lemma_lra

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
