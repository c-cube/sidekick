
(** {1 Profiling probes} *)

type probe

val begin_ : string -> probe

val exit : probe -> unit

val with_ : string -> (unit -> 'a) -> 'a

module type BACKEND = sig
  val get_ts : unit -> float

  val emit_event :
    name : string ->
    start : float ->
    end_ : float ->
    unit ->
    unit

  val teardown : unit -> unit
end

type backend = (module BACKEND)

module Control : sig
  val setup : backend option -> unit

  val teardown : unit -> unit
end
