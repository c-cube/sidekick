(** Registry to extract values *)

type t
type 'a key

val create_key : unit -> 'a key
(** Call this statically, typically at program initialization, for
      each distinct key. *)

val create : unit -> t
val get : t -> 'a key -> 'a option
val set : t -> 'a key -> 'a -> unit
