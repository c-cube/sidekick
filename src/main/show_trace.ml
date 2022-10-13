open Sidekick_core
open Sidekick_trace
module Proof = Sidekick_proof
module Smt = Sidekick_smt_solver

type state = {
  dump: bool;
  src: Source.t;
  t_reader: Smt.Trace_reader.t;
  p_reader: Proof.Trace_reader.t;
}

let show_sat (self : state) ~tag v : unit =
  match tag with
  | "AssCSat" ->
    (match
       Ser_decode.(
         let d =
           let+ id = dict_field "id" int and+ c = dict_field "c" (list int) in
           id, c
         in
         run d v)
     with
    | Ok (id, c) -> Fmt.printf "[%d]: %a@." id Fmt.Dump.(list int) c
    | Error _ -> ())
  | "DelCSat" ->
    (match
       Ser_decode.(
         let d =
           let+ id = dict_field "id" int in
           id
         in
         run d v)
     with
    | Ok id -> Fmt.printf "del [%d]@." id
    | Error _ -> ())
  | "UnsatC" ->
    (match
       Ser_decode.(
         let d =
           let+ id = dict_field "id" int in
           id
         in
         run d v)
     with
    | Ok id -> Fmt.printf "unsat [%d]@." id
    | Error _ -> ())
  | _ -> ()

let show_event (self : state) i ~tag v : unit =
  Log.debugf 10 (fun k ->
      k "(@[show-trace[%d]@ :tag %S@ :val %a@])" i tag Ser_value.pp v);
  if self.dump then Format.printf "[%d]: %S %a@." i tag Ser_value.pp v;

  (match Smt.Trace_reader.decode self.t_reader ~tag v with
  | Some e -> Fmt.printf "[%d]: %a@." i Smt.Trace_reader.pp_entry e
  | None -> ());

  show_sat self ~tag v;
  ()

let show_file ~dump file : unit =
  Log.debugf 1 (fun k -> k "(@[show-file %S@])" file);
  let src = Source.of_string_using_bencode @@ CCIO.File.read_exn file in
  let tst = Term.Store.create () in

  (* trace reader *)
  let t_reader =
    Smt.Trace_reader.create tst src
      ~const_decoders:
        [ Sidekick_core.const_decoders; Sidekick_base.const_decoders ]
  in
  let p_reader =
    Proof.Trace_reader.create ~src (Smt.Trace_reader.term_trace_reader t_reader)
  in

  let st = { t_reader; src; dump; p_reader } in
  Source.iter_all src (fun i ~tag v -> show_event st i ~tag v)

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
