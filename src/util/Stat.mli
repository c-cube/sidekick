
(** {1 Statistics} *)

module Fmt = CCFormat

type t

val create : unit -> t

type 'a counter

val mk_int : t -> string -> int counter
val mk_float : t -> string -> float counter

val incr : int counter -> unit
val incr_f : float counter -> float -> unit

(** Existential counter *)
type ex_counter

val all : t -> ex_counter Iter.t

val pp_all : ex_counter Iter.t Fmt.printer

val global : t
(** Global statistics, by default *)
