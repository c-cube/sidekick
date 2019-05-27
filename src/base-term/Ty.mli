
(** {1 Hashconsed Types} *)

open Base_types

type t = Base_types.ty
type view = Base_types.ty_view
type def = Base_types.ty_def

val id : t -> int
val view : t -> view

val prop : t
val atomic : def -> t list -> t

val atomic_uninterpreted : ID.t -> t

val card : t -> ty_card

val is_prop : t -> bool
val is_uninterpreted : t -> bool

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t
include Intf.PRINT with type t := t

module Tbl : CCHashtbl.S with type key = t

module Fun : sig
  type t = fun_ty

  val args : t -> ty list
  val ret : t -> ty
  val arity : t -> int
  val unfold : t -> ty list * ty

  val mk : ty list -> ty -> t

  include Intf.PRINT with type t := t
end
