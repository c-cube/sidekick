module BL = Sidekick_bin_lib

let clause_of_int_l store atoms : Drup_check.clause =
  atoms |> Iter.of_list
  |> Iter.map Drup_check.Atom.of_int_dimacs
  |> Drup_check.Clause.of_iter store

let check ?pb proof : bool =
  let@ _sp = Profile.with_span ~__FILE__ ~__LINE__ "check" in
  let cstore = Drup_check.Clause.create () in
  let trace = Drup_check.Trace.create cstore in

  (* add problem to trace, if provided *)
  (match pb with
  | None -> ()
  | Some f when Filename.extension f = ".cnf" ->
    let@ _sp = Profile.with_span ~__FILE__ ~__LINE__ "parse-pb.cnf" in
    CCIO.with_in f (fun ic ->
        let parser_ = BL.Dimacs_parser.create ic in
        BL.Dimacs_parser.iter parser_ (fun atoms ->
            let c = clause_of_int_l cstore atoms in
            Drup_check.Trace.add_input_clause trace c))
  | Some f ->
    (* TODO: handle .cnf.gz *)
    Error.errorf "unknown problem file extension '%s'" (Filename.extension f));

  let add_proof_from_chan ic =
    let p = BL.Drup_parser.create_chan ic in
    BL.Drup_parser.iter p (function
      | BL.Drup_parser.Input c ->
        let c = clause_of_int_l cstore c in
        Drup_check.Trace.add_input_clause trace c
      | BL.Drup_parser.Add c ->
        let c = clause_of_int_l cstore c in
        Drup_check.Trace.add_clause trace c
      | BL.Drup_parser.Delete c ->
        let c = clause_of_int_l cstore c in
        Drup_check.Trace.del_clause trace c)
  in

  (* add proof to trace *)
  (match proof with
  | f when Filename.extension f = ".drup" ->
    (* read file *)
    let@ _sp = Profile.with_span ~__FILE__ ~__LINE__ "parse-proof.drup" in
    CCIO.with_in f add_proof_from_chan
  | f when Filename.extension f = ".gz" ->
    (* read compressed proof *)
    let@ _sp = Profile.with_span ~__FILE__ ~__LINE__ "parse-proof.drup" in
    (* TODO: more graceful failure mode here *)
    assert (Filename.extension @@ Filename.chop_extension f = ".drup");
    let cmd = Printf.sprintf "gzip --keep -d -c \"%s\"" f in
    Log.debugf 1 (fun k -> k "command to open proof: %s" cmd);
    let p = Unix.open_process_in cmd in
    CCFun.finally
      ~h:(fun () -> ignore (Unix.close_process_in p))
      ~f:(fun () -> add_proof_from_chan p)
  | f -> Error.errorf "unknown proof file extension '%s'" (Filename.extension f));

  (* check proof *)
  Log.debugf 1 (fun k ->
      k "checking proof (%d steps)" (Drup_check.Trace.size trace));
  match Drup_check.Fwd_check.check trace with
  | Ok () -> true
  | Error err ->
    Format.eprintf "%a@." (Drup_check.Fwd_check.pp_error trace) err;
    false

let () =
  let files = ref [] in
  let opts = [ "-d", Arg.Int Log.set_debug, " set debug level" ] |> Arg.align in
  Printexc.record_backtrace true;
  let@ () = Sidekick_bin_lib.Trace_setup.with_trace in

  let t1 = Unix.gettimeofday () in

  Arg.parse opts (fun f -> files := f :: !files) "checker [opt]* [file]+";

  let ok =
    match List.rev !files with
    | [ pb; proof ] ->
      Log.debugf 1 (fun k -> k "checker: problem `%s`, proof `%s`" pb proof);
      check ~pb proof
    | [ proof ] ->
      Log.debugf 1 (fun k -> k "checker: proof `%s`" proof);
      check ?pb:None proof
    | _ -> Error.errorf "expected <problem>? <proof>"
  in

  let t2 = Unix.gettimeofday () -. t1 in
  Format.printf "c %s@."
    (if ok then
      "OK"
    else
      "FAIL");
  Format.printf "c elapsed time: %.3fs@." t2;
  if not ok then exit 1
