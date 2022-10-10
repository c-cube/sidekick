open Sidekick_core
module Profile = Sidekick_util.Profile
open! Sidekick_base
open Common_

[@@@ocaml.warning "-32"]

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module Fmt = CCFormat

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

type t = {
  progress: Progress_bar.t option;
  solver: Solver.t;
  time_start: float;
  time_limit: float;
  memory_limit: float;
  proof_file: string option;
  pp_model: bool;
  pp_cnf: bool;
  check: bool;
  restarts: bool;
}

(* call the solver to check-sat *)
let create ?(restarts = true) ?(pp_cnf = false) ?proof_file ?(pp_model = false)
    ?(check = false) ?time ?memory ?(progress = false) (solver : Solver.t) : t =
  let time_start = now () in
  let progress =
    if progress then
      Some (Progress_bar.create ())
    else
      None
  in

  let time_limit = Option.value ~default:3600. time in
  (* default: 1 hour *)
  let memory_limit = Option.value ~default:4e9 memory in

  {
    time_start;
    restarts;
    progress;
    solver;
    proof_file;
    pp_model;
    pp_cnf;
    check;
    time_limit;
    memory_limit;
  }

let decl_sort (_self : t) c n : unit =
  (* TODO: more? pass to abstract solver? *)
  Log.debugf 1 (fun k -> k "(@[declare-sort %a@ :arity %d@])" ID.pp c n)

let decl_fun (_self : t) id args ret : unit =
  (* TODO: more? record for model building *)
  Log.debugf 1 (fun k ->
      k "(@[declare-fun %a@ :args (@[%a@])@ :ret %a@])" ID.pp id
        (Util.pp_list Ty.pp) args Ty.pp ret)

(* call the solver to check satisfiability *)
let solve (self : t) ~assumptions () : Solver.res =
  let t1 = now () in
  let should_stop _ _ =
    if now () -. self.time_start > self.time_limit then (
      Log.debugf 0 (fun k -> k "timeout");
      true
    ) else if float (Gc.quick_stat ()).Gc.heap_words *. 8. > self.memory_limit
      then (
      Log.debugf 0 (fun k -> k "%S" "exceeded memory limit");
      true
    ) else
      false
  in

  let on_progress =
    Option.map (fun p _s -> Progress_bar.tick p) self.progress
  in

  let res =
    let@ () = Profile.with_ "process.solve" in
    Solver.solve ~assumptions ?on_progress ~should_stop self.solver
  in
  let t2 = now () in
  flush stdout;
  (match res with
  | Solver.Sat m ->
    if self.pp_model then
      (* TODO: use actual {!Model} in the solver? or build it afterwards *)
      Format.printf "(@[<hv1>model@ %a@])@." Sidekick_smt_solver.Model.pp m;
    (* TODO
       if check then (
         Solver.check_model s;
         CCOpt.iter (fun h -> check_smt_model (Solver.solver s) h m) hyps;
       );
    *)
    let t3 = now () in
    Fmt.printf "sat@.";
    Fmt.printf "; (%.3f/%.3f/%.3f)@." (t1 -. time_start) (t2 -. t1) (t3 -. t2)
  | Solver.Unsat { unsat_step_id; unsat_core = _ } ->
    if self.check then
      ()
    (* FIXME: check trace?
       match proof_opt with
       | Some p ->
         Profile.with_ "unsat.check" (fun () -> Solver.Pre_proof.check p);
       | _ -> ()
    *);

    (match self.proof_file with
    | Some file ->
      (match unsat_step_id () with
      | None -> ()
      | Some step_id ->
        let proof = Solver.proof self.solver in
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

    let t3 = now () in
    Fmt.printf "unsat@.";
    Fmt.printf "; (%.3f/%.3f/%.3f)@." (t1 -. time_start) (t2 -. t1) (t3 -. t2)
  | Solver.Unknown reas ->
    Fmt.printf "unknown@.";
    Fmt.printf "; @[<h>:reason %a@]@." Solver.Unknown.pp reas
  | exception exn ->
    Option.iter Progress_bar.clear_line self.progress;
    raise exn);
  res

let known_logics =
  [ "QF_UF"; "QF_LRA"; "QF_UFLRA"; "QF_DT"; "QF_UFDT"; "QF_LIA"; "QF_UFLIA" ]

(* process a single statement *)
let process_stmt (self : t) (stmt : Statement.t) : unit or_error =
  let@ () = Profile.with_ "smtlib.process-stmt" in
  Log.debugf 5 (fun k ->
      k "(@[smtlib.process-statement@ %a@])" Statement.pp stmt);

  let add_step r = Proof_trace.add_step (Solver.proof self.solver) r in

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
      List.map (fun (sign, t) -> Solver.mk_lit_t self.solver ~sign t) l
    in
    ignore (solve self ~assumptions () : Solver.res);
    E.return ()
  | Statement.Stmt_ty_decl (id, n) ->
    decl_sort self id n;
    E.return ()
  | Statement.Stmt_decl (f, ty_args, ty_ret) ->
    decl_fun self f ty_args ty_ret;
    E.return ()
  | Statement.Stmt_assert t ->
    if self.pp_cnf then Format.printf "(@[<hv1>assert@ %a@])@." Term.pp t;
    let lit = Solver.mk_lit_t self.solver t in
    Solver.add_clause self.solver [| lit |]
      (add_step @@ fun () -> Proof_sat.sat_input_clause [ lit ]);
    E.return ()
  | Statement.Stmt_assert_clause c_ts ->
    if self.pp_cnf then
      Format.printf "(@[<hv1>assert-clause@ %a@])@." (Util.pp_list Term.pp) c_ts;

    let c = CCList.map (fun t -> Solver.mk_lit_t self.solver t) c_ts in

    (* proof of assert-input + preprocessing *)
    let pr =
      add_step @@ fun () ->
      let lits = List.map (Solver.mk_lit_t self.solver) c_ts in
      Proof_sat.sat_input_clause lits
    in

    Solver.add_clause self.solver (CCArray.of_list c) pr;
    E.return ()
  | Statement.Stmt_get_model ->
    (match Solver.last_res self.solver with
    | Some (Solver.Sat m) -> Fmt.printf "%a@." Sidekick_smt_solver.Model.pp m
    | _ -> Error.errorf "cannot access model");
    E.return ()
  | Statement.Stmt_get_value l ->
    (match Solver.last_res self.solver with
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
  | Statement.Stmt_data ds ->
    List.iter (fun d -> Solver.add_ty self.solver (Data_ty.data_as_ty d)) ds;
    E.return ()
  | Statement.Stmt_define _ ->
    (* TODO *)
    Error.errorf "cannot deal with definitions yet"

open Sidekick_base

let th_bool = Th_bool.theory
let th_bool_dyn : Solver.theory = Th_bool.theory_dyn
let th_bool_static : Solver.theory = Th_bool.theory_static
let th_data : Solver.theory = Th_data.theory
let th_lra : Solver.theory = Th_lra.theory
let th_ty_unin = Th_ty_unin.theory
