(** {2 Conversion into {!Term.t}} *)

open Sidekick_core
module Profile = Sidekick_util.Profile
open! Sidekick_base

[@@@ocaml.warning "-32"]

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module Fmt = CCFormat
module Solver = Sidekick_smt_solver.Solver

module Check_cc = struct
  module SI = Sidekick_smt_solver.Solver_internal
  module MCC = Sidekick_mini_cc

  let pp_c out c = Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∨ " Lit.pp) c

  let pp_and out c =
    Fmt.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∧ " Lit.pp) c

  let add_cc_lit (cc : MCC.t) (lit : Lit.t) : unit =
    let t = Lit.term lit in
    MCC.add_lit cc t (Lit.sign lit)

  (* check that this is a proper CC conflict *)
  let check_conflict si _cc (confl : Lit.t list) : unit =
    Log.debugf 15 (fun k -> k "(@[check-cc-conflict@ %a@])" pp_c confl);
    let tst = SI.tst si in
    let cc = MCC.create_default tst in
    (* add [¬confl] and check it's unsat *)
    List.iter (fun lit -> add_cc_lit cc @@ Lit.neg lit) confl;
    if MCC.check_sat cc then
      Error.errorf
        "@[<2>check-cc-conflict:@ @[clause %a@]@ is not a UF tautology \
         (negation is sat)@]"
        pp_c confl
    else
      Log.debugf 15 (fun k -> k "(@[check-cc-conflict.ok@ %a@])" pp_c confl)

  let check_propagation si _cc p reason : unit =
    let reason = reason () in
    Log.debugf 15 (fun k ->
        k "(@[check-cc-prop@ %a@ :reason %a@])" Lit.pp p pp_and reason);
    let tst = SI.tst si in
    let cc = MCC.create_default tst in
    (* add [reason & ¬lit] and check it's unsat *)
    List.iter (add_cc_lit cc) reason;
    add_cc_lit cc (Lit.neg p);
    if MCC.check_sat cc then
      Error.errorf
        "@[<2>check-cc-prop:@ @[%a => %a@]@ is not a UF tautology (negation is \
         sat)@]"
        pp_and reason Lit.pp p
    else
      Log.debugf 15 (fun k ->
          k "(@[check-cc-prop.ok@ @[%a => %a@]@])" pp_and reason Lit.pp p)

  let theory =
    Solver.mk_theory ~name:"cc-check"
      ~create_and_setup:(fun si ->
        let n_calls = Stat.mk_int (SI.stats si) "check-cc.call" in
        SI.on_cc_conflict si (fun { cc; th; c } ->
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

let reset_line = "\x1b[2K\r"

let mk_progress (_s : Solver.t) : _ -> unit =
  let start = Sys.time () in
  let n = ref 0 in
  let syms = "|\\-/" in
  fun _s ->
    let diff = Sys.time () -. start in
    incr n;
    (* TODO: print some core stats in the progress bar
       let n_cl = Solver.pp_stats
    *)
    (* limit frequency *)
    if float !n > 6. *. diff then (
      let sym = String.get syms (!n mod String.length syms) in
      Printf.printf "%s[%.2fs %c]" reset_line diff sym;
      n := 0;
      flush stdout
    )

let with_file_out (file : string) (f : out_channel -> 'a) : 'a =
  if Filename.extension file = ".gz" then (
    let p =
      Unix.open_process_out
        (Printf.sprintf "gzip -c - > \"%s\"" (String.escaped file))
    in
    CCFun.finally1 ~h:(fun () -> Unix.close_process_out p) f p
  ) else
    CCIO.with_out file f

(* call the solver to check-sat *)
let solve ?gc:_ ?restarts:_ ?proof_file ?(pp_model = false) ?(check = false)
    ?time ?memory ?(progress = false) ~assumptions s : Solver.res =
  let t1 = Sys.time () in
  let on_progress =
    if progress then
      Some (mk_progress s)
    else
      None
  in

  let should_stop =
    match time, memory with
    | None, None -> None
    | _ ->
      let time = Option.value ~default:3600. time in
      (* default: 1 hour *)
      let memory = Option.value ~default:4e9 memory in
      (* default: 4 GB *)
      let stop _ _ =
        Sys.time () -. t1 > time
        || (Gc.quick_stat ()).Gc.major_words *. 8. > memory
      in
      Some stop
  in

  let res =
    Profile.with_ "solve" (fun () ->
        Solver.solve ~assumptions ?on_progress ?should_stop s
        (* ?gc ?restarts ?time ?memory ?progress *))
  in
  let t2 = Sys.time () in
  Printf.printf "\r";
  flush stdout;
  (match res with
  | Solver.Sat m ->
    if pp_model then
      (* TODO: use actual {!Model} in the solver? or build it afterwards *)
      Format.printf "(@[<hv1>model@ %a@])@." Sidekick_smt_solver.Model.pp m;
    (* TODO
       if check then (
         Solver.check_model s;
         CCOpt.iter (fun h -> check_smt_model (Solver.solver s) h m) hyps;
       );
    *)
    let t3 = Sys.time () -. t2 in
    Format.printf "Sat (%.3f/%.3f/%.3f)@." t1 (t2 -. t1) t3
  | Solver.Unsat { unsat_step_id; unsat_core = _ } ->
    if check then
      ()
    (* FIXME: check trace?
       match proof_opt with
       | Some p ->
         Profile.with_ "unsat.check" (fun () -> Solver.Pre_proof.check p);
       | _ -> ()
    *);

    (match proof_file with
    | Some file ->
      (match unsat_step_id () with
      | None -> ()
      | Some step_id ->
        let proof = Solver.proof s in
        let proof_quip =
          Profile.with_ "proof.to-quip" @@ fun () -> assert false
          (* TODO
             Proof_quip.of_proof proof ~unsat:step_id
          *)
        in
        Profile.with_ "proof.write-file" @@ fun () ->
        with_file_out file @@ fun oc ->
        (* TODO
           Proof_quip.output oc proof_quip;
        *)
        flush oc)
    | _ -> ());

    let t3 = Sys.time () -. t2 in
    Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2 -. t1) t3
  | Solver.Unknown reas ->
    Format.printf "Unknown (:reason %a)@." Solver.Unknown.pp reas
  | exception exn ->
    Printf.printf "%s%!" reset_line;
    raise exn);
  res

let known_logics =
  [ "QF_UF"; "QF_LRA"; "QF_UFLRA"; "QF_DT"; "QF_UFDT"; "QF_LIA"; "QF_UFLIA" ]

(* process a single statement *)
let process_stmt ?gc ?restarts ?(pp_cnf = false) ?proof_file ?pp_model
    ?(check = false) ?time ?memory ?progress (solver : Solver.t)
    (stmt : Statement.t) : unit or_error =
  Log.debugf 5 (fun k ->
      k "(@[smtlib.process-statement@ %a@])" Statement.pp stmt);
  let decl_sort c n : unit =
    Log.debugf 1 (fun k -> k "(@[declare-sort %a@ :arity %d@])" ID.pp c n)
    (* TODO: more? *)
  in
  let decl_fun id args ret : unit =
    Log.debugf 1 (fun k ->
        k "(@[declare-fun %a@ :args (@[%a@])@ :ret %a@])" ID.pp id
          (Util.pp_list Ty.pp) args Ty.pp ret)
    (* TODO: more? *)
  in

  let add_step r = Proof_trace.add_step (Solver.proof solver) r in

  match stmt with
  | Statement.Stmt_set_logic logic ->
    if not @@ List.mem logic known_logics then
      Log.debugf 0 (fun k -> k "warning: unknown logic `%s`" logic);
    E.return ()
  | Statement.Stmt_set_option l ->
    Log.debugf 0 (fun k ->
        k "warning: unknown option `%a`" (Util.pp_list Fmt.string) l);
    E.return ()
  | Statement.Stmt_set_info _ -> E.return ()
  | Statement.Stmt_exit ->
    Log.debug 1 "exit";
    raise Exit
  | Statement.Stmt_check_sat l ->
    (* FIXME: how to map [l] to [assumptions] in proof? *)
    let assumptions =
      List.map (fun (sign, t) -> Solver.mk_lit_t solver ~sign t) l
    in
    ignore
      (solve ?gc ?restarts ~check ?pp_model ?proof_file ?time ?memory ?progress
         ~assumptions solver
        : Solver.res);
    E.return ()
  | Statement.Stmt_ty_decl (id, n) ->
    decl_sort id n;
    E.return ()
  | Statement.Stmt_decl (f, ty_args, ty_ret) ->
    decl_fun f ty_args ty_ret;
    E.return ()
  | Statement.Stmt_assert t ->
    if pp_cnf then Format.printf "(@[<hv1>assert@ %a@])@." Term.pp t;
    let lit = Solver.mk_lit_t solver t in
    Solver.add_clause solver [| lit |]
      (add_step @@ fun () -> Proof_sat.sat_input_clause [ lit ]);
    E.return ()
  | Statement.Stmt_assert_clause c_ts ->
    if pp_cnf then
      Format.printf "(@[<hv1>assert-clause@ %a@])@." (Util.pp_list Term.pp) c_ts;

    let c = CCList.map (fun t -> Solver.mk_lit_t solver t) c_ts in

    (* proof of assert-input + preprocessing *)
    let pr =
      add_step @@ fun () ->
      let lits = List.map Lit.atom c_ts in
      Proof_sat.sat_input_clause lits
    in

    Solver.add_clause solver (CCArray.of_list c) pr;
    E.return ()
  | Statement.Stmt_get_model ->
    (match Solver.last_res solver with
    | Some (Solver.Sat m) -> Fmt.printf "%a@." Sidekick_smt_solver.Model.pp m
    | _ -> Error.errorf "cannot access model");
    E.return ()
  | Statement.Stmt_get_value l ->
    (match Solver.last_res solver with
    | Some (Solver.Sat m) ->
      let l =
        List.map
          (fun t ->
            match Sidekick_smt_solver.Model.eval m t with
            | None -> Error.errorf "cannot evaluate %a" Term.pp t
            | Some u -> t, u)
          l
      in
      let pp_pair out (t, u) =
        Fmt.fprintf out "(@[%a@ %a@])" Term.pp t Term.pp u
      in
      Fmt.printf "(@[%a@])@." (Util.pp_list pp_pair) l
    | _ -> Error.errorf "cannot access model");
    E.return ()
  | Statement.Stmt_data _ -> E.return ()
  | Statement.Stmt_define _ -> Error.errorf "cannot deal with definitions yet"

module Th_data = SBS.Th_data
module Th_bool = SBS.Th_bool
module Th_lra = SBS.Th_lra

let th_bool : Solver.theory = Th_bool.theory
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
