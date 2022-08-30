type t = private int

include Sidekick_sigs.EQ_ORD_HASH_PRINT with type t := t

type state

val create : unit -> state
val fresh : state -> t

module Set : CCSet.S with type elt = t
