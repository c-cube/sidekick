
(** {1 Linear Integer Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LIA *)

open Sidekick_core
include Intf_lia

module Make(A : ARG) : S with module A = A = struct
  module A = A
  module Ty = A.S.T.Ty
  module T = A.S.T.Term
  module Lit = A.S.Solver_internal.Lit
  module SI = A.S.Solver_internal
  module N = A.S.Solver_internal.CC.N

  module Q = A.Q
  module Z = A.Z

  module LRA_solver = A.LRA_solver

  type state = {
    stat: Stat.t;
    proof: A.S.P.t;
    tst: T.store;
    ty_st: Ty.store;
    lra_solver: LRA_solver.state;
    (* TODO: with intsolver
    encoded_eqs: unit T.Tbl.t; (* [a=b] gets clause [a = b <=> (a >= b /\ a <= b)] *)
    needs_th_combination: unit T.Tbl.t;
    stat_th_comb: int Stat.counter;
       *)
  }

  let create ?(stat=Stat.create()) ~lra_solver proof tst ty_st : state =
    { stat; proof; tst; ty_st;
      lra_solver;
      (*
      encoded_eqs=T.Tbl.create 16;
      needs_th_combination=T.Tbl.create 16;
      stat_th_comb=Stat.mk_int stat "lia.th-comb";
         *)
    }

  let push_level _self =
    (*
    Backtrack_stack.push_level self.local_eqs;
       *)
    ()

  let pop_levels _self _n =
    (*
    Backtrack_stack.pop_levels self.local_eqs n ~f:(fun _ -> ());
       *)
    ()

  (* convert [t] to a real-typed term *)
  let rec conv_to_lra (self:state) (t:T.t) : T.t =
    let open Sidekick_arith_lra in
    let f = conv_to_lra self in
    let mklra = LRA_solver.A.mk_lra self.tst in
    match A.view_as_lia t with
    | LIA_const n ->
      mklra @@ LRA_const (Q.of_bigint n)
    | LIA_pred (p, a, b) ->
      mklra @@ LRA_pred (p, f a, f b)
    | LIA_op (op, a, b) ->
      mklra @@ LRA_op (op, f a, f b)
    | LIA_mult (c, x) ->
      mklra @@ LRA_mult (Q.of_bigint c, f x)
    | LIA_other t ->
      mklra @@ LRA_other (A.mk_to_real self.tst t)

  (* preprocess linear expressions away *)
  let preproc_lia (self:state) si (module PA:SI.PREPROCESS_ACTS)
      (t:T.t) : unit =
    Log.debugf 50 (fun k->k "(@[lia.preprocess@ %a@])" T.pp t);

    match A.view_as_lia t with
    | LIA_pred _ ->
      (* perform LRA relaxation *)
      let u = conv_to_lra self t in
      let pr =
        let lits = [Lit.atom ~sign:false self.tst t; Lit.atom self.tst u] in
        A.lemma_relax_to_lra Iter.(of_list lits) self.proof
      in

      (* add [t => u] *)
      let cl = [PA.mk_lit ~sign:false t; PA.mk_lit u] in
      PA.add_clause cl pr;

    | LIA_other t when A.has_ty_int t ->
      SI.declare_pb_is_incomplete si;
    | LIA_op _ | LIA_mult _ ->
      (* TODO: theory combination?*)
      SI.declare_pb_is_incomplete si;
    | LIA_const _ | LIA_other _ -> ()

  let create_and_setup si =
    Log.debug 2 "(th-lia.setup)";
    let stat = SI.stats si in
    let lra = match SI.Registry.get (SI.registry si) LRA_solver.k_state with
      | None -> Error.errorf "LIA: cannot find LRA, is it registered?"
      | Some st -> st
    in
    let st = create ~stat ~lra_solver:lra
        (SI.proof si) (SI.tst si) (SI.ty_st si) in

    SI.on_preprocess si (preproc_lia st);
    st

  let theory =
    A.S.mk_theory
      ~name:"th-lia"
      ~create_and_setup ~push_level ~pop_levels
      ()
end
