
(** {1 Value}

    Semantic value *)

type t = Solver_types.value

val true_ : t
val false_ : t
val bool : bool -> t

val mk_elt : ID.t -> Ty.t -> t

val is_bool : t -> bool
val is_true : t -> bool
val is_false : t -> bool

include Intf.EQ with type t := t
include Intf.HASH with type t := t
include Intf.PRINT with type t := t


