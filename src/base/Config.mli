(** Configuration *)

module Key : sig
  type 'a t

  val create : unit -> 'a t

  val equal : 'a t -> 'a t -> bool
  (** Compare two keys that have compatible types *)
end

type t

val empty : t
val mem : _ Key.t -> t -> bool
val add : 'a Key.t -> 'a -> t -> t
val length : t -> int
val cardinal : t -> int
val find : 'a Key.t -> t -> 'a option

val find_exn : 'a Key.t -> t -> 'a
(** @raise Not_found if the key is not in the table *)

type pair = Pair : 'a Key.t * 'a -> pair

val iter : (pair -> unit) -> t -> unit
val to_iter : t -> pair Iter.t
val of_iter : pair Iter.t -> t
val add_iter : t -> pair Iter.t -> t
val add_list : t -> pair list -> t
val of_list : pair list -> t
val to_list : t -> pair list
