(** Source to read a trace.

    A source is an IO input source that allows the read of individual
    entries of the trace, by providing their entry ID. It also allows to
    iterate on entries in chronological order.
*)

type tag = string

module type S = sig
  val get_entry : Entry_id.t -> tag * Ser_value.t
  (** @raise Not_found if there is no such entry *)

  val iter_all : (Entry_id.t -> tag:tag -> Ser_value.t -> unit) -> unit
  (** Iterate on all entries *)
end

type t = (module S)

val get_entry : t -> Entry_id.t -> (tag * Ser_value.t) option
val get_entry_exn : t -> Entry_id.t -> tag * Ser_value.t
val iter_all : t -> (Entry_id.t -> tag:tag -> Ser_value.t -> unit) -> unit

val of_string_using_bencode : string -> t
(** Decode string, where entries are offsets *)
