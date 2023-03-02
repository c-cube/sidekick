open Types_

type view = level_view =
  | L_zero
  | L_succ of level
  | L_var of string  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

type t = level

include Sidekick_sigs.EQ_ORD_HASH_PRINT with type t := t

val to_string : t -> string

val as_offset : t -> t * int
(** [as_offset lvl] returns a pair [lvl' + n]. *)

(** Hashconsing store *)
module Store : sig
  type t

  val create : unit -> t
end

type store = Store.t

val zero : store -> t
val one : store -> t
val var : store -> string -> t
val succ : store -> t -> t
val of_int : store -> int -> t
val max : store -> t -> t -> t
val imax : store -> t -> t -> t

(** {2 helpers} *)

val is_zero : t -> bool
val is_one : t -> bool
val is_int : t -> bool
val as_int : t -> int option

(** {2 Judgements}

    These are little proofs of some symbolic properties of levels, even
    those which contain variables. *)

val judge_leq : store -> t -> t -> bool
(** [judge_leq st l1 l2] is [true] if [l1] is proven to be lower
    or equal to [l2] *)

val judge_eq : store -> t -> t -> bool
(** [judge_eq st l1 l2] is [true] iff [judge_leq l1 l2]
    and [judge_leq l2 l1] *)

val judge_is_zero : store -> t -> bool
(** [judge_is_zero st l] is [true] iff [l <= 0] holds *)

val judge_is_nonzero : store -> t -> bool
(** [judge_is_nonzero st l] is [true] iff [1 <= l] holds *)
