(** Uninterpreted constants *)

open Types_

type ty = Term.t
type t = Types_.uconst = { uc_id: ID.t; uc_ty: ty }

val id : t -> ID.t
val ty : t -> ty

type Const.view += private Uconst of t

include Sidekick_sigs.EQ_ORD_HASH_PRINT with type t := t

val const_decoders : Const.decoders

val make : ID.t -> ty -> t
(** Make a new uninterpreted function. *)

val uconst : Term.store -> t -> Term.t
val uconst_of_id : Term.store -> ID.t -> ty -> Term.t
val uconst_of_id' : Term.store -> ID.t -> ty list -> ty -> Term.t
val uconst_of_str : Term.store -> string -> ty list -> ty -> Term.t

module Map : CCMap.S with type key = t
module Tbl : CCHashtbl.S with type key = t
