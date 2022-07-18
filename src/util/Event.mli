type 'a t
(** An event emitting values of type ['a] *)

module Emitter : sig
  type 'a t

  val emit : 'a t -> 'a -> unit
  val create : unit -> 'a t
end

val on : 'a t -> ('a -> unit) -> unit
val of_emitter : 'a Emitter.t -> 'a t
