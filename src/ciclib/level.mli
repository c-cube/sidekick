open Types_

type t = level =
  | L_zero
  | L_succ of level
  | L_var of string  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

include Sidekick_sigs.PRINT with type t := t

val to_string : t -> string

val as_offset : t -> t * int
(** [as_offset lvl] returns a pair [lvl' + n]. *)

val zero : t
val one : t
val var : string -> t
val succ : t -> t
val of_int : int -> t
val max : t -> t -> t
val imax : t -> t -> t

(** {2 helpers} *)

val is_zero : t -> bool
val is_one : t -> bool
val is_int : t -> bool
val as_int : t -> int option

(** {2 Judgements}

    These are little proofs of some symbolic properties of levels, even
    those which contain variables. *)

val judge_leq : t -> t -> bool
(** [judge_leq st l1 l2] is [true] if [l1] is proven to be lower
    or equal to [l2] *)

val judge_eq : t -> t -> bool
(** [judge_eq st l1 l2] is [true] iff [judge_leq l1 l2]
    and [judge_leq l2 l1] *)

val judge_is_zero : t -> bool
(** [judge_is_zero st l] is [true] iff [l <= 0] holds *)

val judge_is_nonzero : t -> bool
(** [judge_is_nonzero st l] is [true] iff [1 <= l] holds *)
