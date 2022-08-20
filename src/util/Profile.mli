(** Profiling probes.

   This basic library can produce Catapult traces (a json file)
   that can be read at [http://ui.perfetto.dev].
 *)

type probe

val null_probe : probe
val enabled : unit -> bool
val instant : ?args:(string * string) list -> string -> unit
val begin_ : string -> probe
val exit : ?args:(string * string) list -> probe -> unit
val with_ : ?args:(string * string) list -> string -> (unit -> 'a) -> 'a
val with1 : ?args:(string * string) list -> string -> ('a -> 'b) -> 'a -> 'b

val with2 :
  ?args:(string * string) list -> string -> ('a -> 'b -> 'c) -> 'a -> 'b -> 'c

val count : string -> (string * int) list -> unit

module type BACKEND = sig
  val get_ts : unit -> float

  val emit_duration_event :
    name:string ->
    start:float ->
    end_:float ->
    args:(string * string) list ->
    unit ->
    unit

  val emit_instant_event :
    name:string -> ts:float -> args:(string * string) list -> unit -> unit

  val emit_count_event : name:string -> ts:float -> (string * int) list -> unit
  val teardown : unit -> unit
end

type backend = (module BACKEND)

module Control : sig
  val setup : backend option -> unit
  val teardown : unit -> unit
end
