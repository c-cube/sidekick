(** Trail *)

type t

val create : unit -> t
val var_at : t -> int -> TVar.t
val push_assignment : t -> TVar.t -> unit

include Sidekick_sigs.BACKTRACKABLE0_CB with type t := t and type elt := TVar.t
