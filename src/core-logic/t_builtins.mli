(** Core builtins *)

open Types_
open Term

type const_view += C_bool | C_eq | C_ite | C_not | C_true | C_false

val bool : store -> t
val c_not : store -> t
val c_eq : store -> t
val c_ite : store -> t
val true_ : store -> t
val false_ : store -> t
val bool_val : store -> bool -> t

val eq : store -> t -> t -> t
(** [eq a b] is [a = b] *)

val not : store -> t -> t

val ite : store -> t -> t -> t -> t
(** [ite a b c] is [if a then b else c] *)

val is_eq : t -> bool
val is_bool : t -> bool

val abs : store -> t -> bool * t
(** [abs t] returns an "absolute value" for the term, along with the
    sign of [t].

    The idea is that we want to turn [not a] into [(false, a)],
    or [(a != b)] into [(false, a=b)]. For terms without a negation this
    should return [(true, t)]. *)

val as_bool_val : t -> bool option
