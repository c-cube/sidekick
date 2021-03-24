(** {2 Conversion into {!Term.t}} *)

module BT = Sidekick_base_term
module Profile = Sidekick_util.Profile
open Sidekick_base_term

[@@@ocaml.warning "-32"]

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module Fmt = CCFormat

(* instantiate solver here *)
module Solver_arg = struct
  module T = Sidekick_base_term

  let cc_view = Term.cc_view
  let is_valid_literal _ = true
  module P = struct
    type t = Default
    let default=Default
    let pp out _ = Fmt.string out "default"
  end
end
module Solver = Sidekick_msat_solver.Make(Solver_arg)

module Check_cc = struct
  module Lit = Solver.Solver_internal.Lit
  module SI = Solver.Solver_internal
  module CC = Solver.Solver_internal.CC
  module MCC = Sidekick_mini_cc.Make(Solver_arg)

  let pp_c out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∨ " Lit.pp) c
  let pp_and out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∧ " Lit.pp) c

  let add_cc_lit (cc:MCC.t) (lit:Lit.t) : unit =
    let t = Lit.term lit in
    MCC.add_lit cc t (Lit.sign lit)

  (* check that this is a proper CC conflict *)
  let check_conflict si _cc (confl:Lit.t list) : unit =
    Log.debugf 15 (fun k->k "(@[check-cc-conflict@ %a@])" pp_c confl);
    let tst = SI.tst si in
    let cc = MCC.create tst in
    (* add [¬confl] and check it's unsat *)
    List.iter (fun lit -> add_cc_lit cc @@ Lit.neg lit) confl;
    if MCC.check_sat cc then (
      Error.errorf "@[<2>check-cc-conflict:@ @[clause %a@]@ \
                    is not a UF tautology (negation is sat)@]" pp_c confl
    ) else (
      Log.debugf 15 (fun k->k "(@[check-cc-conflict.ok@ %a@])" pp_c confl);
    )

  let check_propagation si _cc p reason : unit =
    let reason = reason() in
    Log.debugf 15 (fun k->k "(@[check-cc-prop@ %a@ :reason %a@])" Lit.pp p pp_and reason);
    let tst = SI.tst si in
    let cc = MCC.create tst in
    (* add [reason & ¬lit] and check it's unsat *)
    List.iter (add_cc_lit cc) reason;
    add_cc_lit cc (Lit.neg p);
    if MCC.check_sat cc then (
      Error.errorf "@[<2>check-cc-prop:@ @[%a => %a@]@ \
                    is not a UF tautology (negation is sat)@]" pp_and reason Lit.pp p
    ) else (
      Log.debugf 15
        (fun k->k "(@[check-cc-prop.ok@ @[%a => %a@]@])" pp_and reason Lit.pp p);
    )

  let theory =
    Solver.mk_theory ~name:"cc-check"
      ~create_and_setup:(fun si ->
          let n_calls = Stat.mk_int (Solver.Solver_internal.stats si) "check-cc.call" in
          Solver.Solver_internal.on_cc_conflict si
            (fun cc ~th c ->
               if not th then (
                 Stat.incr n_calls;
                 check_conflict si cc c
               )))
      ()
end

(* TODO: use external proof checker instead: check-sat(φ + model)
(* check SMT model *)
let check_smt_model (solver:Solver.Sat_solver.t) (hyps:_ Vec.t) (m:Model.t) : unit =
  Log.debug 1 "(smt.check-smt-model)";
  let module S = Solver.Sat_solver in
  let check_atom (lit:Lit.t) : Msat.lbool =
    Log.debugf 5 (fun k->k "(@[smt.check-smt-model.atom@ %a@])" Lit.pp lit);
    let a = S.make_atom solver lit in
    let sat_value = S.eval_atom solver a in
    let t, sign = Lit.as_atom lit in
    begin match Model.eval m t with
      | Some (V_bool b) ->
        let b = if sign then b else not b in
        if (sat_value <> Msat.L_undefined) &&
           ((b && sat_value=Msat.L_false) || (not b && sat_value=Msat.L_true)) then (
          Error.errorf "(@[check-model.error@ :atom %a@ :model-val %B@ :sat-val %a@])"
            S.Atom.pp a b Msat.pp_lbool sat_value
        ) else (
          Log.debugf 5
            (fun k->k "(@[check-model@ :atom %a@ :model-val %B@ :sat-val %a@])"
                S.Atom.pp a b Msat.pp_lbool sat_value);
        )
      | Some v ->
        Error.errorf "(@[check-model.error@ :atom %a@ :non-bool-value %a@])"
          S.Atom.pp a Value.pp v
      | None ->
        if sat_value <> Msat.L_undefined then (
          Error.errorf "(@[check-model.error@ :atom %a@ :no-smt-value@ :sat-val %a@])"
            S.Atom.pp a Msat.pp_lbool sat_value
        );
    end;
    sat_value
  in
  let check_c c =
    let bs = List.map check_atom c in
    if List.for_all (function Msat.L_true -> false | _ -> true) bs then (
      Error.errorf "(@[check-model.error.none-true@ :clause %a@ :vals %a@])"
        (Fmt.Dump.list Lit.pp) c Fmt.(Dump.list @@ Msat.pp_lbool) bs
    );
  in
  Vec.iter check_c hyps
   *)

let mk_progress (_s:Solver.t) : _ -> unit =
  let start = Sys.time() in
  let n = ref 0 in
  let syms = "|\\-/" in
  fun _s ->
    let diff = Sys.time() -. start in
    incr n;
    (* TODO: print some core stats in the progress bar
    let n_cl = Solver.pp_stats
       *)
    (* limit frequency *)
    if float !n > 6. *. diff then (
      let sym = String.get syms (!n mod String.length syms) in
      Printf.printf "\r[%.2fs %c]" diff sym;
      n := 0;
      flush stdout
    )

(* call the solver to check-sat *)
let solve
    ?gc:_
    ?restarts:_
    ?dot_proof
    ?(pp_model=false)
    ?(check=false)
    ?time:_ ?memory:_ ?(progress=false)
    ?hyps:_
    ~assumptions
    s : unit =
  let t1 = Sys.time() in
  let on_progress =
    if progress then Some (mk_progress s) else None in
  let res =
    Profile.with_ "solve" begin fun () ->
      Solver.solve ~assumptions ?on_progress s
    (* ?gc ?restarts ?time ?memory ?progress *)
    end
  in
  let t2 = Sys.time () in
  Printf.printf "\r"; flush stdout;
  begin match res with
    | Solver.Sat m ->
      if pp_model then (
        (* TODO: use actual {!Model} in the solver? or build it afterwards *)
        Format.printf "(@[<hv1>model@ %a@])@." Solver.Model.pp m
      );
      (* TODO
      if check then (
        Solver.check_model s;
        CCOpt.iter (fun h -> check_smt_model (Solver.solver s) h m) hyps;
      );
         *)
      let t3 = Sys.time () -. t2 in
      Format.printf "Sat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    | Solver.Unsat {proof;_} ->
      if check then (
        match proof with
        | lazy (Some p) ->
          Profile.with_ "unsat.check" (fun () -> Solver.Proof.check p);
        | _ -> ()
      );
      begin match dot_proof, proof with
        | None, _ ->  ()
        | Some file, lazy (Some p) ->
          Profile.with_ "dot.proof" @@ fun () ->
          CCIO.with_out file
            (fun oc ->
               Log.debugf 1 (fun k->k "write proof into `%s`" file);
               let fmt = Format.formatter_of_out_channel oc in
               Solver.Proof.pp_dot fmt p;
               Format.pp_print_flush fmt (); flush oc)
        | _ -> ()
      end;
      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    | Solver.Unknown reas ->
      Format.printf "Unknown (:reason %a)" Solver.Unknown.pp reas
  end

(* process a single statement *)
let process_stmt
    ?hyps
    ?gc ?restarts ?(pp_cnf=false) ?dot_proof ?pp_model ?(check=false)
    ?time ?memory ?progress
    (solver:Solver.t)
    (stmt:Statement.t) : unit or_error =
  Log.debugf 5
    (fun k->k "(@[smtlib.process-statement@ %a@])" Statement.pp stmt);
  let decl_sort c n : unit =
    Log.debugf 1 (fun k->k "(@[declare-sort %a@ :arity %d@])" ID.pp c n);
    (* TODO: more? *)
  in
  let decl_fun id args ret : unit =
    Log.debugf 1
      (fun k->k "(@[declare-fun %a@ :args (@[%a@])@ :ret %a@])"
          ID.pp id (Util.pp_list Ty.pp) args Ty.pp ret);
    (* TODO: more? *)
  in
  begin match stmt with
    | Statement.Stmt_set_logic ("QF_UF"|"QF_LRA"|"QF_UFLRA"|"QF_DT") ->
      E.return ()
    | Statement.Stmt_set_logic s ->
      Log.debugf 0 (fun k->k "warning: unknown logic `%s`" s);
      E.return ()
    | Statement.Stmt_set_option l ->
      Log.debugf 0 (fun k->k "warning: unknown option `%a`" (Util.pp_list Fmt.string) l);
      E.return ()
    | Statement.Stmt_set_info _ -> E.return ()
    | Statement.Stmt_exit ->
      Log.debug 1 "exit";
      raise Exit
    | Statement.Stmt_check_sat l ->
      let assumptions =
        List.map (fun (sign,t) -> Solver.mk_atom_t solver ~sign t) l
      in
      solve
        ?gc ?restarts ?dot_proof ~check ?pp_model ?time ?memory ?progress
        ~assumptions ?hyps
        solver;
      E.return()
    | Statement.Stmt_ty_decl (id,n) ->
      decl_sort id n;
      E.return ()
    | Statement.Stmt_decl (f,ty_args,ty_ret) ->
      decl_fun f ty_args ty_ret;
      E.return ()
    | Statement.Stmt_assert t ->
      if pp_cnf then (
        Format.printf "(@[<hv1>assert@ %a@])@." Term.pp t
      );
      let atom = Solver.mk_atom_t solver t in
      CCOpt.iter (fun h -> Vec.push h [atom]) hyps;
      Solver.add_clause solver (IArray.singleton atom);
      E.return()
    | Statement.Stmt_assert_clause c ->
      if pp_cnf then (
        Format.printf "(@[<hv1>assert-clause@ %a@])@." (Util.pp_list Term.pp) c
      );
      let c = List.map (Solver.mk_atom_t solver) c in
      CCOpt.iter (fun h -> Vec.push h c) hyps;
      Solver.add_clause solver (IArray.of_list c);
      E.return()
    | Statement.Stmt_data _ ->
      E.return()
    | Statement.Stmt_define _ ->
      Error.errorf "cannot deal with definitions yet"
  end

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
  end)

module Th_bool = Sidekick_th_bool_static.Make(struct
  module S = Solver
  type term = S.T.Term.t
  include Form
end)

module Th_lra = Sidekick_arith_lra.Make(struct
  module S = Solver
  module T = BT.Term
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

  module Gensym = struct
    type t = {
      tst: T.state;
      mutable fresh: int;
    }

    let create tst : t = {tst; fresh=0}
    let tst self = self.tst
    let copy s = {s with tst=s.tst}

    let fresh_term (self:t) ~pre (ty:Ty.t) : T.t =
      let name = Printf.sprintf "_sk_lra_%s%d" pre self.fresh in
      self.fresh <- 1 + self.fresh;
      let id = ID.make name in
      BT.Term.const self.tst @@ Fun.mk_undef_const id ty
  end
end)

let th_bool : Solver.theory = Th_bool.theory
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
