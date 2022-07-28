(** Constants.

  Constants are logical symbols, defined by the user thanks to an open type *)

type t
type view = ..

module type DYN_OPS = sig
  val pp : view Fmt.printer
  val equal : view -> view -> bool
  val hash : view -> int
end

type ops = (module DYN_OPS)

val view : t -> view
val make : view -> ops -> t

include EQ_HASH_PRINT with type t := t
