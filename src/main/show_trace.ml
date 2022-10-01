open Sidekick_trace

let show_file file : unit =
  Log.debugf 1 (fun k -> k "(@[show-file %S@])" file);
  let src = Source.of_string_using_bencode @@ CCIO.File.read_exn file in
  Source.iter_all src (fun i ~tag v ->
      Format.printf "[%d]: %S %a@." i tag Sidekick_util.Ser_value.pp v)

let () =
  let files = ref [] in
  let opts =
    [
      ( "--bt",
        Arg.Unit (fun () -> Printexc.record_backtrace true),
        " enable backtraces" );
    ]
    |> Arg.align
  in
  Arg.parse opts (fun f -> files := f :: !files) "show_trace [file]+";
  let files = List.rev !files in
  List.iter show_file files
