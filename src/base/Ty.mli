open Types_

include module type of struct
  include Term
end

type t = ty
type data = Types_.data

include Sidekick_sigs.EQ_ORD_HASH_PRINT with type t := t

val bool : store -> t
val real : store -> t
val int : store -> t
val uninterpreted : store -> ID.t -> t
val is_uninterpreted : t -> bool
val is_real : t -> bool
val is_int : t -> bool

(* TODO: separate functor?
      val finite : t -> bool
      val set_finite : t -> bool -> unit
   val args : t -> ty list
   val ret : t -> ty
   val arity : t -> int
   val unfold : t -> ty list * ty
*)
