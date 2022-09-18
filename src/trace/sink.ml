(** An IO sink for traces.

    A trace is emitted on the fly into a sink. The sink collects or
    writes entries that are emitted into it.
*)

module type S = sig
  val emit : Write_value.t -> Entry_id.t
end

type t = (module S)
(** Trace sink *)

let[@inline] emit (module Sink : S) (v : Write_value.t) : Entry_id.t =
  Sink.emit v

let[@inline] emit' (self : t) v : unit = ignore (emit self v : Entry_id.t)

let bencode_buf_ (buf:Buffer.t) (v:Write_value.t) : unit =

  let[@inline] char c = Buffer.add_char buf c in
  let[@inline] str s = Buffer.add_string buf s in
  let[@inline] int i = Printf.bprintf buf "%d" i in

    let rec enc_v (v:Write_value.t) : unit =
      let module V = Write_value in
      match v with
      | V.Int i -> char 'i'; int i; char 'e'
      | V.Bool true -> str "i1e"
      | V.Bool false -> str "i0e"
      | V.Str s | Bytes s ->
          int (String.length s);
          char ':';
          str s
      | V.List l ->
          char 'l';
          List.iter (fun v -> enc_v (v ())) l;
          char 'e'
      | V.Dict l ->
          char 'd';
          List.iter (fun (k,v) ->
            enc_v (V.string k);
            enc_v (v ())) l;
          char 'e'
    in
    enc_v v

(** A sink that emits entries using Bencode into the given channel *)
let of_out_channel_using_bencode (oc: out_channel): t =
  let id_ = ref 0 in
  let buf = Buffer.create 128 in
  (module struct
    let emit (v:Write_value.t) =
      assert (Buffer.length buf = 0);
      let id = Entry_id.Internal_.make !id_ in
      incr id_;
      bencode_buf_ buf v;
      Buffer.output_buffer oc buf;
      Buffer.clear buf;
      id

  end)
