open Sidekick_trace
module Str_const = Sidekick_core_logic.Str_const
module Tracer = Term.Tracer
module Trace_reader = Term.Trace_reader

let store = Term.Store.create ()

open struct
  let type_ = Term.type_ store

  let l =
    CCSeq.unfold (fun ty -> Some (ty, Term.ty ty)) type_
    |> CCSeq.take 5 |> CCSeq.to_list

  let bool = Term.bool store
  let a = Term.const store @@ Str_const.make "a" ~ty:bool
  let a' = Term.const store @@ Str_const.make "a" ~ty:bool
  let b = Term.const store @@ Str_const.make "b" ~ty:bool
  let ty_b2b = Term.arrow store bool bool
  let p = Term.const store @@ Str_const.make "p" ~ty:ty_b2b
  let q = Term.const store @@ Str_const.make "q" ~ty:ty_b2b
  let pa = Term.app store p a
  let pb = Term.app store p b
  let qa = Term.app store q a
  let qb = Term.app store q b
end

let buf = Buffer.create 32
let tracer = Tracer.create ~sink:(Sink.of_buffer_using_bencode buf) ()
let id_pa = Tracer.emit tracer pa
let id_pa' = Tracer.emit tracer pa;;

assert (Entry_id.equal id_pa id_pa');;

Printf.printf "buf containing pa: %s\n(len %d)\n%!" (Buffer.contents buf)
  (String.length @@ Buffer.contents buf)

(* now decode *)

let trace_reader =
  Trace_reader.create
    ~const_decoders:[ Term.const_decoders; Str_const.const_decoders ]
    ~source:(Source.of_string_using_bencode (Buffer.contents buf))
    store

let () =
  match Trace_reader.read_term trace_reader id_pa with
  | Ok t -> Fmt.printf "read pa: %a@." Term.pp t
  | Error e -> Fmt.printf "could not read pa: %s" e
