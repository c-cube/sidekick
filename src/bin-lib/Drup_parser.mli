
(** {1 DRUP parser} *)

type t

type event =
  | Add of int list
  | Delete of int list

val create : in_channel -> t

val next : t -> event option

val iter : t -> event Iter.t


