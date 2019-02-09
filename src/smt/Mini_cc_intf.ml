
type ('f, 't, 'ts) view =
  | Bool of bool
  | App of 'f * 'ts
  | If of 't * 't * 't

(* TODO: also HO app, Eq, Distinct cases?
   -> then API that just adds boolean terms and does the right thing in case of
   Eq/Distinct *)

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
    val pp : t Fmt.printer

    (** View the term through the lens of the congruence closure *)
    val view : t -> (Fun.t, t, t Sequence.t) view
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

