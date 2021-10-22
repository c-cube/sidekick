
module CS = Chunk_stack
module Proof_ser = Sidekick_base_proof_trace.Proof_ser

let parse_file (file:string) : unit =
  Log.debugf 2 (fun k->k"parsing file %S" file);

  CS.Reader.with_file_backward file @@ fun reader ->

  let n = ref 0 in
  let rec display_steps () =
    CS.Reader.next reader
      ~finish:(fun () -> ())
      ~yield:(fun b i _len ->
          let decode = {Proof_ser.Bare.Decode.bs=b; off=i} in
          let step = Proof_ser.Step.decode decode in
          incr n;
          Format.printf "@[<2>%a@]@." Proof_ser.Step.pp step;
          display_steps();
        );
  in
  display_steps();
  Format.printf "read %d steps@." !n;
  ()

let () =
  let file = ref "" in
  let opts = [
    "--bt", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable stack traces";
    "-d", Arg.Int Log.set_debug, "<lvl> sets the debug verbose level";
  ] |> Arg.align in
  Arg.parse opts (fun f -> file := f) "proof-trace-dump <file>";
  if !file = "" then failwith "please provide a file";

  parse_file !file
