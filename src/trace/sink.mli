(** An IO sink for traces.

    A trace is emitted on the fly into a sink. The sink collects or
    writes entries that are emitted into it.
*)

module type S = sig
  val emit : Write_value.t -> Entry_id.t
end

type t = (module S)
(** Trace sink *)

val emit : t -> Write_value.t -> Entry_id.t

val emit' : t -> Write_value.t -> unit

(** A sink that emits entries using Bencode into the given channel *)
val of_out_channel_using_bencode : out_channel -> t

