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

module type EQ_HASH_PRINT = sig
  include EQ
  include HASH with type t := t
  include PRINT with type t := t
end

module type EQ_ORD_HASH_PRINT = sig
  include EQ
  include ORD with type t := t
  include HASH with type t := t
  include PRINT with type t := t
end

type 'a printer = Format.formatter -> 'a -> unit
