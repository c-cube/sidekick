
module BL = Sidekick_bin_lib

let clause_of_int_l store atoms : Drup_check.clause =
  atoms
  |> CCList.map Drup_check.Atom.of_int_dimacs
  |> Drup_check.Clause.of_list store

let check ?pb proof : bool =
  Profile.with_ "check" @@ fun() ->
  let cstore = Drup_check.Clause.create() in
  let trace = Drup_check.Trace.create cstore in

  (* add problem to trace, if provided *)
  begin match pb with
    | None -> ()
    | Some f when Filename.extension f = ".cnf" ->
      Profile.with_ "parse-pb.cnf" @@ fun() ->
      CCIO.with_in f
        (fun ic ->
           let parser_ = BL.Dimacs_parser.create ic in
           BL.Dimacs_parser.iter parser_
             (fun atoms ->
                let c = clause_of_int_l cstore atoms in
                Drup_check.Trace.add_input_clause trace c))
    | Some f ->
      (* TODO: handle .cnf.gz *)
      Error.errorf "unknown problem file extension '%s'" (Filename.extension f)
  end;

  (* add proof to trace *)
  begin match proof with
    | f when Filename.extension f = ".drup" ->
      Profile.with_ "parse-proof.drup" @@ fun() ->
      CCIO.with_in f
        (fun ic ->
           let p = BL.Drup_parser.create_chan ic in
           BL.Drup_parser.iter p
             (function
               | BL.Drup_parser.Input c ->
                 let c = clause_of_int_l cstore c in
                 Drup_check.Trace.add_input_clause trace c
               | BL.Drup_parser.Add c ->
                 let c = clause_of_int_l cstore c in
                 Drup_check.Trace.add_clause trace c
               | BL.Drup_parser.Delete c ->
                 let c = clause_of_int_l cstore c in
                 Drup_check.Trace.del_clause trace c))
    | f ->
      (* TODO: handle .drup.gz *)
      Error.errorf "unknown proof file extension '%s'" (Filename.extension f)
  end;

  (* check proof *)
  Log.debugf 1 (fun k->k"checking proof (%d steps)" (Drup_check.Trace.size trace));
  begin match Drup_check.Fwd_check.check trace with
    | Ok () -> true
    | Error err ->
      Format.eprintf "%a@." (Drup_check.Fwd_check.pp_error trace) err;
      false
  end

let () =
  let files = ref [] in
  let opts = [
    "-d", Arg.Int Log.set_debug, " set debug level";
  ] |> Arg.align in
  Printexc.record_backtrace true;
  Sidekick_tef.setup();

  Arg.parse opts (fun f -> files := f :: !files) "checker [opt]* [file]+";

  let ok =
    match List.rev !files with
    | [pb; proof] ->
      Log.debugf 1 (fun k->k"checker: problem `%s`, proof `%s`" pb proof);
      check ~pb proof
    | [proof] ->
      Log.debugf 1 (fun k->k"checker: proof `%s`" proof);
      check ?pb:None proof
    | _ -> Error.errorf "expected <problem>? <proof>"
  in

  let t2 = Mtime_clock.elapsed () |> Mtime.Span.to_s in
  Format.printf "c %s@." (if ok then "OK" else "FAIL");
  Format.printf "c elapsed time: %.3fs@." t2;
  if not ok then exit 1
