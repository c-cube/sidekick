
module CS = Chunk_stack
module Proof_ser = Sidekick_base_proof_trace.Proof_ser

let file = ref ""
let quiet = ref false

let parse_file () : unit =
  Log.debugf 2 (fun k->k"parsing file %S" !file);

  CS.Reader.with_file_backward !file @@ fun reader ->

  let n = ref 0 in
  let rec display_steps () =
    CS.Reader.next reader
      ~finish:(fun () -> ())
      ~yield:(fun b i _len ->
          let decode = {Proof_ser.Bare.Decode.bs=b; off=i} in
          let step = Proof_ser.Step.decode decode in
          incr n;
          if not !quiet then (
            Format.printf "@[<2>%a@]@." Proof_ser.Step.pp step;
          );
          display_steps();
        );
  in
  display_steps();
  Format.printf "read %d steps@." !n;
  ()

let () =
  let opts = [
    "--bt", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable stack traces";
    "-d", Arg.Int Log.set_debug, "<lvl> sets the debug verbose level";
    "-q", Arg.Set quiet, " quiet: do not print steps";
  ] |> Arg.align in
  Arg.parse opts (fun f -> file := f) "proof-trace-dump <file>";
  if !file = "" then failwith "please provide a file";

  parse_file ()
