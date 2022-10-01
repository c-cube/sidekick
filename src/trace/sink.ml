(** An IO sink for traces.

    A trace is emitted on the fly into a sink. The sink collects or
    writes entries that are emitted into it.
*)

type tag = string

module type S = sig
  val emit : tag:tag -> Ser_value.t -> Entry_id.t
end

type t = (module S)

let[@inline] emit (module Sink : S) ~tag (v : Ser_value.t) : Entry_id.t =
  Sink.emit v ~tag

let[@inline] emit' (self : t) ~tag v : unit =
  ignore (emit self ~tag v : Entry_id.t)

let null : t =
  (module struct
    let emit ~tag:_ _ = Entry_id.dummy
  end)

let of_out_channel_using_bencode (oc : out_channel) : t =
  let id_ = ref 0 in
  let buf = Buffer.create 128 in
  (module struct
    let emit ~tag (v : Ser_value.t) =
      assert (Buffer.length buf = 0);
      let id = Entry_id.of_int_unsafe !id_ in
      (* add tag+id around *)
      let v' = Ser_value.(list [ int id; string tag; v ]) in
      incr id_;
      Sidekick_bencode.Encode.to_buffer buf v';
      Buffer.add_char buf '\n';
      Buffer.output_buffer oc buf;
      Buffer.clear buf;
      id
  end)

let of_buffer_using_bencode (buf : Buffer.t) : t =
  (module struct
    let emit ~tag (v : Ser_value.t) =
      let id = Entry_id.of_int_unsafe @@ Buffer.length buf in
      (* add tag+id around *)
      let v' = Ser_value.(list [ int id; string tag; v ]) in
      Sidekick_bencode.Encode.to_buffer buf v';
      Buffer.add_char buf '\n';
      id
  end)
