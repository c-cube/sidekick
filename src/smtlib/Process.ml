(** {2 Conversion into {!Term.t}} *)

module BT = Sidekick_base
module Profile = Sidekick_util.Profile
open Sidekick_base
module SBS = Sidekick_base_solver

[@@@ocaml.warning "-32"]

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module Fmt = CCFormat

module Solver = SBS.Solver

module Check_cc = struct
  module Lit = Solver.Solver_internal.Lit
  module SI = Solver.Solver_internal
  module CC = Solver.Solver_internal.CC
  module MCC = Sidekick_mini_cc.Make(SBS.Solver_arg)

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
    ?(pp_model=false)
    ?proof_file
    ?(check=false)
    ?time:_ ?memory:_ ?(progress=false)
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
    | Solver.Unsat _ ->

      if check then (
        ()
        (* FIXME: check trace?
        match proof_opt with
        | Some p ->
          Profile.with_ "unsat.check" (fun () -> Solver.Pre_proof.check p);
        | _ -> ()
           *)
      );

      (* FIXME: instead, create a proof if proof file or --check is given
      begin match proof_file, proof with
        | Some file, lazy (Some p) ->
          Profile.with_ "proof.write-file" @@ fun () ->
          let p = Profile.with1 "proof.mk-proof" Solver.Pre_proof.to_proof p in
          CCIO.with_out file
            (fun oc -> Proof.Quip.output oc p; flush oc)
        | _ -> ()
      end;
         *)

      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;

    | Solver.Unknown reas ->
      Format.printf "Unknown (:reason %a)" Solver.Unknown.pp reas
  end

(* process a single statement *)
let process_stmt
    ?gc ?restarts ?(pp_cnf=false)
    ?proof_file ?pp_model ?(check=false)
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
    | Statement.Stmt_set_logic ("QF_UF"|"QF_LRA"|"QF_UFLRA"|"QF_DT"|"QF_UFDT") ->
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
      (* FIXME: how to map [l] to [assumptions] in proof? *)
      let assumptions =
        List.map
          (fun (sign,t) -> Solver.mk_lit_t solver ~sign t)
          l
      in
      solve
        ?gc ?restarts ~check ?proof_file ?pp_model
        ?time ?memory ?progress
        ~assumptions
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
      let lit = Solver.mk_lit_t solver t in
      Solver.add_clause solver (IArray.singleton lit)
        (Solver.P.emit_input_clause (Iter.singleton lit));
      E.return()

    | Statement.Stmt_assert_clause c_ts ->
      if pp_cnf then (
        Format.printf "(@[<hv1>assert-clause@ %a@])@." (Util.pp_list Term.pp) c_ts
      );

      let c = CCList.map (fun t -> Solver.mk_lit_t solver t) c_ts in

      (* proof of assert-input + preprocessing *)
      let emit_proof p =
        let module P = Solver.P in
        let tst = Solver.tst solver in
        P.emit_input_clause (Iter.of_list c_ts |> Iter.map (Lit.atom tst)) p;
        P.emit_redundant_clause (Iter.of_list c) p;
      in

      Solver.add_clause solver (IArray.of_list c) emit_proof;
      E.return()

    | Statement.Stmt_data _ ->
      E.return()
    | Statement.Stmt_define _ ->
      Error.errorf "cannot deal with definitions yet"
  end

module Th_data = SBS.Th_data
module Th_bool = SBS.Th_bool
module Th_lra = SBS.Th_lra

let th_bool : Solver.theory = Th_bool.theory
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
