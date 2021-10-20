
(** Manage a list of chunks.

    A chunk is used for serializing proof traces, possibly on disk.
    This way we do not have to keep the whole proof in memory.
    Each chunk is typically one step of the proof search.

    We produce chunks in forward order (chronological order of their discovery),
    but once we find a proof of "false", we work our way backward to find
    chunks transitively needed by this proof of false.
    Once we obtain this subset of the chunks (as a graph in memory) we can
    emit a proper proof with no redundant information.
*)

(** A hand made buffer *)
module Buf : sig
  type t = {
    mutable b: bytes;
    mutable len: int;
  }

  val create : ?cap:int -> unit -> t

  val clear : t -> unit

  val contents : t -> string
end

(** Create a stack of chunks. *)
module Writer : sig
  type t

  val dummy : t

  val into_buf : Buf.t -> t

  val into_channel: out_channel -> t

  val add_buf : t -> Buf.t -> unit

  val add_bytes : t -> bytes -> int -> int -> unit

  val add_string : t -> string -> unit

  val add_buffer : t -> Buffer.t -> unit
end

module Reader : sig
  type t

  val next : t -> yield:(bytes -> int -> int -> 'a) -> finish:(unit -> 'a) -> 'a
  (** Read next chunk, call [yield] with a slice of bytes, otherwise call [finish()]. *)

  val next_string : t -> string option
  (** Read next chunk as a string *)

  val empty : t

  val from_buf : Buf.t -> t

  val from_channel_backward : ?close_at_end:bool -> in_channel -> t
  (** Read channel from the end, assuming that is possible. *)

  val with_file_backward : string -> (t -> 'a) -> 'a
  (** [read_file_backward filename f] calls [f] with an iterator
      over chunks of the file, read from the end.

      Each chunk is assumed to be followed by its length as an int32 LE. *)
end
