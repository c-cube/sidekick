(** Integer-based identifiers. *)

module type S = sig
  type t = private int

  include Sidekick_sigs.EQ_ORD_HASH_PRINT with type t := t

  val to_int : t -> int
  val of_int_unsafe : int -> t
end

(** Generate a new type for integer identifiers *)
module Make () = struct
  type t = int

  let equal : t -> t -> bool = ( = )
  let compare : t -> t -> int = compare
  let hash = CCHash.int
  let pp = CCFormat.int
  let[@inline] to_int i = i

  external of_int_unsafe : int -> t = "%identity"
end
