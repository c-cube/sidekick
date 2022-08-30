(** {1 A backtracking stack} *)

type 'a t

val create : unit -> 'a t

val push : 'a t -> 'a -> unit
(** Push an element onto the stack *)

val push_if_nonzero_level : 'a t -> 'a -> unit
(** Push an element onto the stack if level > 0 *)

include Sidekick_sigs.BACKTRACKABLE1_CB with type 'a t := 'a t

val iter : f:('a -> unit) -> 'a t -> unit
