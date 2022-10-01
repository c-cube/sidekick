type t = Ser_value.t

module Encode : sig
  val to_buffer : Buffer.t -> t -> unit
  val to_string : t -> string
end

module Decode : sig
  val of_string : ?idx:int -> string -> (int * t) option
  (** Decode string, and also return how  many bytes were consumed.
      @param idx initial index (default 0) *)

  val of_string_exn : ?idx:int -> string -> int * t
  (** Parse string.
      @raise Error.Error if the string is not valid bencode. *)
end
