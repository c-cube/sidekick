open Sidekick_core
module Pred = Arith_types_.LRA_pred
module Op = Arith_types_.LRA_op
module View = Arith_types_.LRA_view

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
