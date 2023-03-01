module T = Sidekick_core_logic.Term

let ( let@ ) = ( @@ )

let process_files (files : string list) : unit =
  let st = T.Store.create ~size:1024 () in
  Log.debugf 1 (fun k ->
      k "(@[process-files %a@])" Fmt.Dump.(list string) files);

  let proc_file (file : string) : unit =
    let@ ic = CCIO.with_in file in
    Parse.parse (`In ic)
      (module struct
        let ns _ _ = ()
        let ni _ _ = ()
      end)
  in

  List.iter proc_file files;
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
