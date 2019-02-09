
type ('f, 't) view =
  | Bool of bool
  | App of 'f * 't list
  | If of 't * 't * 't

type res =
  | Sat
  | Unsat

module type ARG = sig
  module Fun : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  module Term : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val view : t -> (Fun.t, t) view
    val pp : t Fmt.printer
  end
end

module type S = sig
  type term
  type fun_

  type t

  val create : unit -> t

  val merge : t -> term -> term -> unit
  val distinct : t -> term list -> unit

  val check : t -> res
end

