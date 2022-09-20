(** An IO sink for traces.

    A trace is emitted on the fly into a sink. The sink collects or
    writes entries that are emitted into it.
*)

module type S = sig
  val emit : tag:string -> Ser_value.t -> Entry_id.t
end

type t = (module S)
(** Trace sink *)

let[@inline] emit (module Sink : S) ~tag (v : Ser_value.t) : Entry_id.t =
  Sink.emit v ~tag

let[@inline] emit' (self : t) ~tag v : unit =
  ignore (emit self ~tag v : Entry_id.t)

(** A sink that emits entries using Bencode into the given channel *)
let of_out_channel_using_bencode (oc : out_channel) : t =
  let id_ = ref 0 in
  let buf = Buffer.create 128 in
  (module struct
    let emit ~tag (v : Ser_value.t) =
      assert (Buffer.length buf = 0);
      let id = Entry_id.Internal_.make !id_ in
      (* add tag+id around *)
      let v' =
        Ser_value.(dict_of_list [ "id", int !id_; "T", string tag; "v", v ])
      in
      incr id_;
      Sidekick_bencode.Encode.to_buffer buf v';
      Buffer.output_buffer oc buf;
      Buffer.clear buf;
      id
  end)
