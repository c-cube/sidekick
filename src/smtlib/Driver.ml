module Profile = Sidekick_util.Profile
module Proof = Sidekick_proof
module Asolver = Solver.Asolver
open! Sidekick_base
open Common_

[@@@ocaml.warning "-32"]

type 'a or_error = ('a, string) CCResult.t

module E = CCResult
module Fmt = CCFormat

type t = {
  progress: Progress_bar.t option;
  solver: Asolver.t;
  build_model: Build_model.t;
  asserts: Term.t Vec.t;
  time_start: float;
  time_limit: float;
  memory_limit: float;
  proof_file: string option;
  pp_model: bool;
  pp_cnf: bool;
  check: bool;
}

(* call the solver to check-sat *)
let create ?(pp_cnf = false) ?proof_file ?(pp_model = false) ?(check = false)
    ?time ?memory ?(progress = false) (solver : Asolver.t) : t =
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
    build_model = Build_model.create ();
    asserts = Vec.create ();
    progress;
    solver;
    proof_file;
    pp_model;
    pp_cnf;
    check;
    time_limit;
    memory_limit;
  }

let decl_sort (self : t) c n ty_const : unit =
  Log.debugf 1 (fun k ->
      k "(@[declare-sort %a@ :arity %d@ :ty-const %a@])" ID.pp c n Term.pp
        ty_const);
  Build_model.add_ty self.build_model ty_const

let decl_fun (self : t) f args ret const : unit =
  Log.debugf 1 (fun k ->
      k "(@[declare-fun %a@ :args (@[%a@])@ :ret %a@ :const %a@])" ID.pp f
        (Util.pp_list Ty.pp) args Ty.pp ret Term.pp const);
  Build_model.add_fun self.build_model const

let build_model (self : t) (sat : Solver.sat_result) : Model.t =
  Build_model.build self.build_model sat

(* FIXME *)
let check_model (_self : t) (_m : Model.t) : unit =
  Log.debugf 0 (fun k -> k "; TODO: check model");
  ()

(* call the solver to check satisfiability *)
let solve (self : t) ~assumptions () : Solver.res =
  let t1 = now () in
  let should_stop _n =
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
    let@ _sp = Profile.with_span ~__FILE__ ~__LINE__ "process.solve" in
    Asolver.solve ~assumptions ?on_progress ~should_stop self.solver ()
  in
  let t2 = now () in
  flush stdout;
  (match res with
  | Asolver.Check_res.Sat sat ->
    if self.pp_model then (
      let m = build_model self sat in
      if self.check then check_model self m;
      Fmt.printf "%a@." Model.pp m
    );
    let t3 = now () in
    Fmt.printf "sat@.";
    Fmt.printf "; (%.3f/%.3f/%.3f)@." (t1 -. time_start) (t2 -. t1) (t3 -. t2)
  | Asolver.Check_res.Unsat { unsat_proof; unsat_core = _ } ->
    if self.check then
      ()
    (* FIXME: check trace?
       match proof_opt with
       | Some p ->
         Profile.with_ "unsat.check" (fun () -> Solver.Pre_proof.check p);
       | _ -> ()
    *);

    (match self.proof_file with
    | Some _file ->
      (match unsat_proof () with
      | None -> ()
      | Some _step_id ->
        (* TODO: read trace; emit proof
              let proof = Solver.proof self.solver in
              let proof_quip =
                Profile.with_ "proof.to-quip" @@ fun () -> assert false
                   Proof_quip.of_proof proof ~unsat:step_id
              Profile.with_ "proof.write-file" @@ fun () ->
              with_file_out file @@ fun oc ->
                 Proof_quip.output oc proof_quip;
           flush oc
        *)
        ())
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
  let@ _sp = Profile.with_span ~__FILE__ ~__LINE__ "smtlib.process-stmt" in
  Log.debugf 5 (fun k ->
      k "(@[smtlib.process-statement@ %a@])" Statement.pp stmt);

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
      List.map (fun (sign, t) -> Asolver.lit_of_term self.solver ~sign t) l
    in
    ignore (solve self ~assumptions () : Solver.res);
    E.return ()
  | Statement.Stmt_ty_decl { name; arity; ty_const } ->
    decl_sort self name arity ty_const;
    E.return ()
  | Statement.Stmt_decl { name; ty_args; ty_ret; const } ->
    decl_fun self name ty_args ty_ret const;
    E.return ()
  | Statement.Stmt_assert t ->
    if self.pp_cnf then Format.printf "(@[<hv1>assert@ %a@])@." Term.pp t;
    if self.check then Vec.push self.asserts t;
    let lit = Asolver.lit_of_term self.solver t in
    Asolver.assert_clause self.solver [| lit |] (fun () ->
        Proof.Sat_rules.sat_input_clause [ lit ]);
    E.return ()
  | Statement.Stmt_assert_clause c_ts ->
    if self.pp_cnf then
      Format.printf "(@[<hv1>assert-clause@ %a@])@." (Util.pp_list Term.pp) c_ts;

    if self.check then
      Vec.push self.asserts (Form.or_l (Asolver.tst self.solver) c_ts);
    let c = CCList.map (fun t -> Asolver.lit_of_term self.solver t) c_ts in

    (* proof of assert-input + preprocessing *)
    let pr () =
      let lits = List.map (Asolver.lit_of_term self.solver) c_ts in
      Proof.Sat_rules.sat_input_clause lits
    in

    Asolver.assert_clause self.solver (CCArray.of_list c) pr;
    E.return ()
  | Statement.Stmt_get_model ->
    (match Asolver.last_res self.solver with
    | Some (Solver.Sat sat) ->
      let m = build_model self sat in
      if self.check then check_model self m;
      Fmt.printf "%a@." Model.pp m
    | _ -> Error.errorf "cannot access model");
    E.return ()
  | Statement.Stmt_get_value l ->
    (match Asolver.last_res self.solver with
    | Some (Solver.Sat sat) ->
      let m = build_model self sat in
      let l =
        List.map
          (fun t ->
            match Model.eval t m with
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
    List.iter
      (fun d -> Asolver.add_ty self.solver ~ty:(Data_ty.data_as_ty d))
      ds;
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
