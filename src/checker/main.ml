
module BL = Sidekick_bin_lib
module SDrup = Sidekick_drup

let clause_of_int_l atoms : SDrup.clause =
  Array.of_list atoms
  |> Array.map SDrup.Atom.of_int
  |> SDrup.Clause.of_array

let check ?pb proof : bool =
  let trace = SDrup.Trace.create() in

  (* add problem to trace, if provided *)
  begin match pb with
    | None -> ()
    | Some f when Filename.extension f = ".cnf" ->
      CCIO.with_in f
        (fun ic ->
           let parser_ = BL.Dimacs_parser.create ic in
           BL.Dimacs_parser.iter parser_
             (fun atoms ->
                let c = clause_of_int_l atoms in
                SDrup.Trace.add_input_clause trace c))
    | Some f ->
      (* TODO: handle .cnf.gz *)
      Error.errorf "unknown problem file extension '%s'" (Filename.extension f)
  end;

  (* add proof to trace *)
  begin match proof with
    | f when Filename.extension f = ".drup" ->
      CCIO.with_in f
        (fun ic ->
           let p = BL.Drup_parser.create ic in
           BL.Drup_parser.iter p
             (function
               | BL.Drup_parser.Add c ->
                 let c = clause_of_int_l c in
                 SDrup.Trace.add_clause trace c
               | BL.Drup_parser.Delete c ->
                 let c = clause_of_int_l c in
                 SDrup.Trace.del_clause trace c))
    | f ->
      (* TODO: handle .drup.gz *)
      Error.errorf "unknown proof file extension '%s'" (Filename.extension f)
  end;

  (* check proof *)
  Log.debugf 1 (fun k->k"checking proof (%d steps)" (SDrup.Trace.size trace));
  begin match SDrup.Fwd_check.check trace with
    | Ok () -> true
    | Error bad ->
      assert (VecI32.size bad > 0);
      let n0 = VecI32.get bad 0 in
      Format.eprintf
        "checking failed on %d events.@.@[<2>First failure is event[%d]:@ %a@]@."
        (VecI32.size bad) n0
        SDrup.Trace.pp_event (SDrup.Trace.get trace n0);
      false
  end

let () =
  let files = ref [] in
  let opts = [
    "-d", Arg.Int Log.set_debug, " set debug level";
  ] |> Arg.align in
  Printexc.record_backtrace true;

  Arg.parse opts (fun f -> files := f :: !files) "checker [opt]* [file]+";

  begin match List.rev !files with
    | [pb; proof] ->
      Log.debugf 1 (fun k->k"checker: problem `%s`, proof `%s`" pb proof);
      let ok = check ~pb proof in
      if not ok then exit 1
    | [proof] ->
      Log.debugf 1 (fun k->k"checker: proof `%s`" proof);
      let ok = check ?pb:None proof in
      if not ok then exit 1
    | _ -> failwith "expected <problem>? <proof>"
  end
