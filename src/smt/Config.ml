
(** {1 Configuration} *)

type 'a sequence = ('a -> unit) -> unit

module Key = CCHet.Key

type pair = CCHet.pair =
  | Pair : 'a Key.t * 'a -> pair

include CCHet.Map
