open Sidekick_core
open Sidekick_trace
module Smt = Sidekick_smt_solver

let show_file ~dump file : unit =
  Log.debugf 1 (fun k -> k "(@[show-file %S@])" file);
  let src = Source.of_string_using_bencode @@ CCIO.File.read_exn file in
  let tst = Term.Store.create () in

  (* trace reader *)
  let t_reader =
    Smt.Trace_reader.create tst src
      ~const_decoders:
        [
          Term.const_decoders; Box.const_decoders; Sidekick_base.const_decoders;
        ]
  in

  Source.iter_all src (fun i ~tag v ->
      Log.debugf 10 (fun k ->
          k "(@[show-trace[%d]@ :tag %S@ :val %a@])" i tag Ser_value.pp v);
      if dump then Format.printf "[%d]: %S %a@." i tag Ser_value.pp v;

      match Smt.Trace_reader.decode t_reader ~tag v with
      | Some e -> Fmt.printf "[%d]: %a@." i Smt.Trace_reader.pp_entry e
      | None -> ())

let () =
  let files = ref [] in
  let dump = ref false in
  let opts =
    [
      "--dump", Arg.Set dump, " dump each raw entry";
      ( "--bt",
        Arg.Unit (fun () -> Printexc.record_backtrace true),
        " enable backtraces" );
      "-d", Arg.Int Log.set_debug, " debug level";
    ]
    |> Arg.align
  in
  Arg.parse opts (fun f -> files := f :: !files) "show_trace [file]+";
  let files = List.rev !files in
  List.iter (show_file ~dump:!dump) files
