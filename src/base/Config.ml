(** {1 Configuration} *)

type 'a sequence = ('a -> unit) -> unit

module Key = Het.Key

type pair = Het.pair = Pair : 'a Key.t * 'a -> pair

include Het.Map
