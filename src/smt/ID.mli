
(* This file is free software. See file "license" for more details. *)

(** {1 Unique Identifiers} *)

type t

val make : string -> t
val makef : ('a, Format.formatter, unit, t) format4 -> 'a
val copy : t -> t

val id : t -> int

val to_string : t -> string
val to_string_full : t -> string

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t
include Intf.PRINT with type t := t

val pp_name : t CCFormat.printer

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t
