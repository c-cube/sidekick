
(* This file is free software. See file "license" for more details. *)

module type EQ = sig
  type t
  val equal : t -> t -> bool
end

module type ORD = sig
  type t
  val compare : t -> t -> int
end

module type HASH = sig
  type t
  val hash : t -> int
end

module type PRINT = sig
  type t
  val pp : t CCFormat.printer
end

type 'a printer = Format.formatter -> 'a -> unit
