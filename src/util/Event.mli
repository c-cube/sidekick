type 'a t
(** An event emitting values of type ['a] *)

module Emitter : sig
  type 'a t

  val create : unit -> 'a t
  val emit : 'a t -> 'a -> unit
end

val on : 'a t -> f:('a -> unit) -> unit
val of_emitter : 'a Emitter.t -> 'a t
val emit : 'a Emitter.t -> 'a -> unit
