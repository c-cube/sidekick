
(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

type 'a printer = 'a CCFormat.printer

val pp_list : ?sep:string -> 'a printer -> 'a list printer

val pp_seq : ?sep:string -> 'a printer -> 'a Sequence.t printer

val pp_array : ?sep:string -> 'a printer -> 'a array printer

val pp_pair : ?sep:string -> 'a printer -> 'b printer -> ('a * 'b) printer

val pp_iarray : ?sep:string -> 'a CCFormat.printer -> 'a IArray.t CCFormat.printer

exception Error of string

val errorf : ('a, Format.formatter, unit, 'b) format4 -> 'a
(** @raise Error when called *)
