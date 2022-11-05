(** Trail *)

type t

val create : unit -> t
val get : t -> int -> TVar.t
val size : t -> int
val push_assignment : t -> TVar.t -> unit
val head : t -> int
val set_head : t -> int -> unit

include Sidekick_sigs.BACKTRACKABLE0_CB with type t := t and type elt := TVar.t
