module T = Sidekick_core_logic.Term

let ( let@ ) = ( @@ )

let process_files (files : string list) : unit =
  let start = Mtime_clock.now () in
  let st = T.Store.create ~size:1024 () in
  Log.debugf 1 (fun k ->
      k "(@[process-files %a@])" Fmt.Dump.(list string) files);

  let n_lines = ref 0 in

  let proc_file (file : string) : unit =
    let@ ic = CCIO.with_in file in
    Parse.parse (`In ic)
      (module struct
        let line _ = incr n_lines
        let ns _ _ = ()
        let ni _ _ = ()
      end)
  in

  List.iter proc_file files;

  let elapsed =
    (Mtime.span (Mtime_clock.now ()) start |> Mtime.Span.to_float_ns) /. 1e9
  in
  Log.debugf 1 (fun k ->
      k "number of lines processed: %d in %.4fs (%.2f/s)" !n_lines elapsed
        (float !n_lines /. elapsed));
  ()

let () =
  let files = ref [] in
  let opts =
    [
      "--debug", Arg.Int Log.set_debug, " set debug level";
      "-d", Arg.Int Log.set_debug, " like --debug";
    ]
    |> Arg.align
  in

  Arg.parse opts (CCList.Ref.push files) "leancheck file+";
  if !files = [] then failwith "provide at least one file";

  process_files (List.rev !files)
