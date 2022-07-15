(** {1 A backtracking stack} *)

type 'a t

val create : unit -> 'a t

val push : 'a t -> 'a -> unit
(** Push an element onto the stack *)

val push_if_nonzero_level : 'a t -> 'a -> unit
(** Push an element onto the stack if level > 0 *)

val n_levels : _ t -> int
(** Number of levels *)

val push_level : _ t -> unit
(** Push a backtracking point *)

val pop_levels : 'a t -> int -> f:('a -> unit) -> unit
(** [pop_levels st n ~f] removes [n] levels, calling [f] on every removed item *)

val iter : f:('a -> unit) -> 'a t -> unit
