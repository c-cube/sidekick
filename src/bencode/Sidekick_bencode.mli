type t = Ser_value.t

module Encode : sig
  val to_buffer : Buffer.t -> t -> unit
  val to_string : t -> string
end

module Decode : sig
  val of_string : string -> t option

  val of_string_exn : string -> t
  (** Parse string.
      @raise Error.Error if the string is not valid bencode. *)
end
