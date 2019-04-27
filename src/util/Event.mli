
(** {1 Observer pattern} *)

type 'a t

val on : 'a t -> ('a -> unit) -> unit

module Emitter : sig
  type 'a t

  val fire : 'a t -> 'a -> unit
end

val make : unit -> 'a t * 'a Emitter.t

