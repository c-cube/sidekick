
module type S = sig
  type elt
  type t

  val create : ?cap:int -> unit -> t

  val size : t -> int

  val clear : t -> unit

  val is_empty : t -> bool

  val push : t -> elt -> unit

  val pop : t -> elt

  val get : t -> int -> elt

  val set : t -> int -> elt -> unit

  val shrink : t -> int -> unit

  val iter : f:(int -> unit) -> t -> unit
  val iteri : f:(int -> elt -> unit) -> t -> unit

  val to_iter : t -> elt Iter.t

  val pp : t CCFormat.printer
end
