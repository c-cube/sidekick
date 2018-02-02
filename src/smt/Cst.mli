
open Solver_types

type t = cst
val id : t -> ID.t
val ty : t -> Ty.t
val make_cstor : ID.t -> Ty.t -> data_cstor lazy_t -> t
val make_proj : ID.t -> Ty.t -> data_cstor lazy_t -> int -> t
val make_tester : ID.t -> Ty.t -> data_cstor lazy_t -> t
val make_defined : ID.t -> Ty.t -> term lazy_t -> cst_defined_info -> t
val make_undef : ID.t -> Ty.t -> t
val arity : t -> int (* number of args *)
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val as_undefined : t -> (t * Ty.t) option
val as_undefined_exn : t -> t * Ty.t
val is_finite_cstor : t -> bool
val pp : t Fmt.printer
module Map : CCMap.S with type key = t
module Tbl : CCHashtbl.S with type key = t
