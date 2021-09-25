
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
  let mk_eqn = Term.eq
  let is_valid_literal _ = true
  module P = Proof_stub
  type proof = P.t
end

(** SMT solver, obtained from {!Sidekick_smt_solver} *)
module Solver = Sidekick_smt_solver.Make(Solver_arg)

(** Theory of datatypes *)
module Th_data = Sidekick_th_data.Make(struct
    module S = Solver
    open! Base_types
    open! Sidekick_th_data
    module Proof = Proof_stub
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

    let lemma_isa_disj p lits = Proof.lemma_isa_disj p lits
    let lemma_isa_split p lits = Proof.lemma_isa_split p lits
    let lemma_cstor_inj p lits = Proof.lemma_cstor_inj p lits
  end)

(** Reducing boolean formulas to clauses *)
module Th_bool = Sidekick_th_bool_static.Make(struct
  module S = Solver
  type term = S.T.Term.t
  include Form
  let lemma_bool_tauto = Proof_stub.lemma_bool_tauto
  let lemma_bool_c = Proof_stub.lemma_bool_c
  let lemma_bool_equiv = Proof_stub.lemma_bool_equiv
  let lemma_ite_true = Proof_stub.lemma_ite_true
  let lemma_ite_false = Proof_stub.lemma_ite_false
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
    | T.Eq (a,b) when Ty.equal (T.ty a) (Ty.real()) ->
      LRA_pred (Eq, a, b)
    | _ -> LRA_other t

  let ty_lra _st = Ty.real()
  let has_ty_real t = Ty.equal (T.ty t) (Ty.real())

  let lemma_lra = Proof_stub.lemma_lra

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

module Th_dyn_trans = Sidekick_th_dyn_trans.Make(struct
    module Solver = Solver
    type term = Solver.T.Term.t
    let config = Sidekick_th_dyn_trans.default_config
    let term_as_eqn _tst t =
      match Term.view t with
      | Term.Eq(a,b) -> Some (a,b)
      | _ -> None
    let mk_eqn tst t u : term = Term.make tst (Term.Eq (t,u))
    let proof_trans lits p = Proof_stub.lemma_cc (Iter.of_list lits) p
    end)

let th_bool : Solver.theory = Th_bool.theory
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
let th_dyn_trans : Solver.theory = Th_dyn_trans.theory
