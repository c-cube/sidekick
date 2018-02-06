
(** {1 Hashconsed Types} *)

type t = Solver_types.ty
type cell = Solver_types.ty_cell
type def = Solver_types.ty_def

val view : t -> cell

val prop : t
val atomic : ID.t -> def -> card:Ty_card.t lazy_t -> t
val arrow : t -> t -> t
val arrow_l : t list -> t -> t

val is_prop : t -> bool
val is_data : t -> bool
val is_uninterpreted : t -> bool
val is_arrow : t -> bool
val unfold : t -> t list * t
val unfold_n : t -> int * t

val mangle : t -> string

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t
include Intf.PRINT with type t := t

module Tbl : CCHashtbl.S with type key = t

