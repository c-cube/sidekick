
open Solver_types

type view = cst_view
type t = cst

val id : t -> ID.t
val view : t -> view
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val as_undefined : t -> (t * Ty.Fun.t) option
val as_undefined_exn : t -> t * Ty.Fun.t

val mk_undef : ID.t -> Ty.Fun.t -> t
val mk_undef_const : ID.t -> Ty.t -> t

val pp : t Fmt.printer
module Map : CCMap.S with type key = t
module Tbl : CCHashtbl.S with type key = t
