
(** {1 Hashconsed Types} *)

open Solver_types

type t = Solver_types.ty

type cell = Solver_types.ty_cell =
  | Prop
  | Atomic of ID.t * ty_def
  | Arrow of ty * ty

type def = Solver_types.ty_def =
  | Uninterpreted
  | Data of datatype
and datatype = Solver_types.datatype = {
  data_cstors: data_cstor ID.Map.t lazy_t;
}
(* a constructor *)
and data_cstor = Solver_types.data_cstor = {
  cstor_ty: ty;
  cstor_args: ty IArray.t; (* argument types *)
  cstor_proj: cst IArray.t lazy_t; (* projectors *)
  cstor_test: cst lazy_t; (* tester *)
  cstor_cst: cst; (* the cstor itself *)
  cstor_card: ty_card; (* cardinality of the constructor('s args) *)
}


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

