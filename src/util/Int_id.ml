
module type S = sig
  type t = private int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t
end

module Make() = struct
  type t = int
  let equal : t -> t -> bool = (=)
  let compare : t -> t -> int = compare
  let hash = CCHash.int
  let[@inline] to_int i = i
  external of_int_unsafe : int -> t = "%identity"
end
