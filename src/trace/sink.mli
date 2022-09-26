(** An IO sink for serialization/tracing

    A trace is emitted on the fly into a sink. The sink collects or
    writes entries that are emitted into it.
*)

type tag = string

module type S = sig
  val emit : tag:tag -> Ser_value.t -> Entry_id.t
end

type t = (module S)
(** Trace sink *)

val emit : t -> tag:tag -> Ser_value.t -> Entry_id.t
val emit' : t -> tag:tag -> Ser_value.t -> unit

val of_out_channel_using_bencode : out_channel -> t
(** A sink that emits entries using Bencode into the given channel *)

val of_buffer_using_bencode : Buffer.t -> t
(** Emit entries into the given buffer, in Bencode. *)
