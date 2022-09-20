(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

type 'a printer = 'a CCFormat.printer

val pp_list : ?sep:string -> 'a printer -> 'a list printer
val pp_iter : ?sep:string -> 'a printer -> 'a Iter.t printer
val pp_array : ?sep:string -> 'a printer -> 'a array printer
val pp_pair : ?sep:string -> 'a printer -> 'b printer -> ('a * 'b) printer
val flat_map_l_arr : ('a -> 'b array) -> 'a list -> 'b list

val array_of_list_map : ('a -> 'b) -> 'a list -> 'b array
(** [array_of_list_map f l] is the same as [Array.of_list @@ List.map f l] *)

val array_to_list_map : ('a -> 'b) -> 'a array -> 'b list
val lazy_map : ('a -> 'b) -> 'a lazy_t -> 'b lazy_t
val lazy_map2 : ('a -> 'b -> 'c) -> 'a lazy_t -> 'b lazy_t -> 'c lazy_t
val array_iteri2 : f:(int -> 'a -> 'b -> unit) -> 'a array -> 'b array -> unit

val setup_gc : unit -> unit
(** Change parameters of the GC *)

module Int_set : CCSet.S with type elt = int
module Int_map : CCMap.S with type key = int
module Int_tbl : CCHashtbl.S with type key = int
module Str_tbl : CCHashtbl.S with type key = string
module Str_map : CCMap.S with type key = string
