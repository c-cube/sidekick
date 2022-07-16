(** Basics *)
module type BASE_RO = sig
  type elt
  type t

  val size : t -> int
  val get : t -> int -> elt
  val iter : f:(elt -> unit) -> t -> unit
  val iteri : f:(int -> elt -> unit) -> t -> unit
  val to_iter : t -> elt Iter.t
end

module type BASE = sig
  include BASE_RO

  val create : ?cap:int -> unit -> t
  val clear : t -> unit
  val copy : t -> t
  val is_empty : t -> bool
  val push : t -> elt -> unit

  val fast_remove : t -> int -> unit
  (** Remove element at index [i] without preserving order
      (swap with last element) *)

  val filter_in_place : (elt -> bool) -> t -> unit
  val ensure_size : t -> int -> unit
  val pop : t -> elt
  val set : t -> int -> elt -> unit
  val shrink : t -> int -> unit
end

module type EXTENSIONS = sig
  type elt
  type t

  val to_array : t -> elt array
  val fold_left : ('a -> elt -> 'a) -> 'a -> t -> 'a
  val pp : elt CCFormat.printer -> t CCFormat.printer
end

module type S = sig
  include BASE
  include EXTENSIONS with type t := t and type elt := elt
end

module Make_extensions (B : BASE_RO) :
  EXTENSIONS with type t := B.t and type elt := B.elt = struct
  include B

  let to_array self =
    if size self = 0 then
      [||]
    else (
      let a = Array.make (size self) (get self 0) in
      iteri self ~f:(Array.set a);
      a
    )

  let fold_left f acc self =
    let r = ref acc in
    iter self ~f:(fun x -> r := f !r x);
    !r

  let pp ppx out self =
    Format.fprintf out "[@[";
    iteri self ~f:(fun i x ->
        if i > 0 then Format.fprintf out ",@ ";
        ppx out x);
    Format.fprintf out "@]]"
end
