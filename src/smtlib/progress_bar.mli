(** Super simple progress bar *)

type t

val create : unit -> t
val tick : t -> unit
val clear_line : t -> unit
