(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

type 'a printer = 'a CCFormat.printer

val pp_list : ?sep:string -> 'a printer -> 'a list printer

val pp_iter : ?sep:string -> 'a printer -> 'a Iter.t printer

val pp_array : ?sep:string -> 'a printer -> 'a array printer

val pp_pair : ?sep:string -> 'a printer -> 'b printer -> ('a * 'b) printer

val pp_iarray : ?sep:string -> 'a CCFormat.printer -> 'a IArray.t CCFormat.printer

val flat_map_l_ia : ('a -> 'b IArray.t) -> 'a list -> 'b list

val setup_gc : unit -> unit
(** Change parameters of the GC *)

module Int_set : CCSet.S with type elt = int
module Int_map : CCMap.S with type key = int
module Int_tbl : CCHashtbl.S with type key = int
