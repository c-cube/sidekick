type ('a, 'b) t
(** An event emitting values of type ['a], where subscribers
    return values of type ['b]. *)

module Emitter : sig
  type ('a, 'b) t

  val create : unit -> ('a, 'b) t
  val emit : ('a, unit) t -> 'a -> unit
  val emit_collect : ('a, 'b) t -> 'a -> 'b list
  val emit_iter : ('a, 'b) t -> 'a -> f:('b -> unit) -> unit
end

val on : ('a, 'b) t -> f:('a -> 'b) -> unit
val of_emitter : ('a, 'b) Emitter.t -> ('a, 'b) t
val emit : ('a, unit) Emitter.t -> 'a -> unit
val emit_collect : ('a, 'b) Emitter.t -> 'a -> 'b list
val emit_iter : ('a, 'b) Emitter.t -> 'a -> f:('b -> unit) -> unit
