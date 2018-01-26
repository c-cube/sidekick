
(** {1 Type Cardinality} *)

open CDCL

type t = Solver_types.ty_card

val (+) : t -> t -> t
val ( * ) : t -> t -> t
val ( ^ ) : t -> t -> t
val finite : t
val infinite : t

val sum : t list -> t
val product : t list -> t

val equal : t -> t -> bool
val compare : t -> t -> int
val pp : t Intf.printer
