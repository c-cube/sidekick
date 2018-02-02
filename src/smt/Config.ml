
(** {1 Configuration} *)

type 'a sequence = ('a -> unit) -> unit

module Key = Het_map.Key

type pair = Het_map.pair =
  | Pair : 'a Key.t * 'a -> pair

include Het_map.Map
