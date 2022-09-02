open Types_

type select = Types_.select = {
  select_id: ID.t;
  select_cstor: cstor;
  select_ty: ty lazy_t;
  select_i: int;
}

type cstor = Types_.cstor = {
  cstor_id: ID.t;
  cstor_is_a: ID.t;
  mutable cstor_arity: int;
  cstor_args: select list lazy_t;
  cstor_ty_as_data: data;
  cstor_ty: ty lazy_t;
}

type t = data = {
  data_id: ID.t;
  data_cstors: cstor ID.Map.t lazy_t;
  data_as_ty: ty lazy_t;
}

type Const.view +=
  private
  | Data of data
  | Cstor of cstor
  | Select of select
  | Is_a of cstor

include Sidekick_sigs.EQ_HASH_PRINT with type t := t

module Select : sig
  type t = select

  include Sidekick_sigs.EQ_HASH_PRINT with type t := t
end

module Cstor : sig
  type t = cstor

  val ty_args : t -> ty list
  val select_idx : t -> int -> select

  include Sidekick_sigs.EQ_HASH_PRINT with type t := t
end

val data : Term.store -> t -> Term.t
val cstor : Term.store -> cstor -> Term.t
val select : Term.store -> select -> Term.t
val is_a : Term.store -> cstor -> Term.t
val data_as_ty : t -> ty

(* TODO: select_ : store -> cstor -> int -> term *)

val as_data : ty -> data option
val as_select : term -> select option
val as_cstor : term -> cstor option
val as_is_a : term -> cstor option
