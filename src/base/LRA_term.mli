open Sidekick_core

module Pred : sig
  type t = Sidekick_th_lra.Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  include Sidekick_sigs.EQ_HASH_PRINT with type t := t
end

module Op : sig
  type t = Sidekick_th_lra.op = Plus | Minus

  include Sidekick_sigs.EQ_HASH_PRINT with type t := t
end

val const_decoders : Const.decoders

module View : sig
  type ('num, 'a) lra_view = ('num, 'a) Sidekick_th_lra.lra_view =
    | LRA_pred of Pred.t * 'a * 'a
    | LRA_op of Op.t * 'a * 'a
    | LRA_mult of 'num * 'a
    | LRA_const of 'num
    | LRA_other of 'a

  type 'a t = (Q.t, 'a) Sidekick_th_lra.lra_view

  val map : f_c:(Q.t -> Q.t) -> ('a -> 'b) -> 'a t -> 'b t
  val iter : ('a -> unit) -> 'a t -> unit
  val pp : pp_t:'a Fmt.printer -> 'a t Fmt.printer
  val hash : sub_hash:('a -> int) -> 'a t -> int
  val equal : sub_eq:('a -> 'b -> bool) -> 'a t -> 'b t -> bool
end

type term = Term.t
type ty = Term.t

val term_of_view : Term.store -> term View.t -> term
val real : Term.store -> ty
val has_ty_real : term -> bool
val pred : Term.store -> Pred.t -> term -> term -> term
val mult_by : Term.store -> Q.t -> term -> term
val op : Term.store -> Op.t -> term -> term -> term
val const : Term.store -> Q.t -> term

(** {2 Helpers} *)

val leq : Term.store -> term -> term -> term
val lt : Term.store -> term -> term -> term
val geq : Term.store -> term -> term -> term
val gt : Term.store -> term -> term -> term
val eq : Term.store -> term -> term -> term
val neq : Term.store -> term -> term -> term
val plus : Term.store -> term -> term -> term
val minus : Term.store -> term -> term -> term

(** {2 View} *)

val view : term -> term View.t
(** View as LRA *)
