(** Free variable *)

open Types_

type t = var = { v_name: string; v_ty: term }

include EQ_ORD_HASH_PRINT with type t := t

val pp_with_ty : t Fmt.printer
val make : string -> term -> t
val makef : ('a, Format.formatter, unit, t) format4 -> term -> 'a
val name : t -> string
val ty : t -> term

include WITH_SET_MAP_TBL with type t := t
