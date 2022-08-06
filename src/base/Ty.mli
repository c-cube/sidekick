open Types_

include module type of struct
  include Term
end

type t = ty
type data = Types_.data

val bool : store -> t
val real : store -> t
val int : store -> t
val uninterpreted : store -> ID.t -> t
val data : store -> data -> t
val is_uninterpreted : t -> bool

(* TODO: separate functor?
      val finite : t -> bool
      val set_finite : t -> bool -> unit
   val args : t -> ty list
   val ret : t -> ty
   val arity : t -> int
   val unfold : t -> ty list * ty
*)
