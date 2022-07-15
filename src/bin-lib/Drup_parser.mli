(** {1 DRUP parser} *)

type t
type event = Input of int list | Add of int list | Delete of int list

val create_chan : in_channel -> t
val create_string : string -> t
val next : t -> event option
val iter : t -> event Iter.t
