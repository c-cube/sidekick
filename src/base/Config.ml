(** Configuration *)

module Key = Het.Key

type pair = Het.pair = Pair : 'a Key.t * 'a -> pair

include Het.Map
