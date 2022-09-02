(** Delayed Theory Combination *)

open Sidekick_core

type t

val create : ?stat:Stat.t -> Term.store -> t

val claim_sort : t -> th_id:Theory_id.t -> ty:Term.t -> unit
(** [claim_sort ~th_id ~ty] means that type [ty] is handled by
    theory [th_id]. A foreign term is a term handled by theory [T1] but
    which occurs inside a term handled by theory [T2 != T1] *)

val claimed_by : t -> ty:Term.t -> Theory_id.t option
(** Find what theory claimed this type, if any *)

val add_term_needing_combination : t -> Term.t -> unit
(** [add_term_needing_combination self t] means that [t] occurs as a foreign
  variable in another term, so it is important that its theory, and the
  theory in which it occurs, agree on it being equal to other
  foreign terms. *)

val pop_new_lits : t -> Lit.t list
(** Get the new literals that the solver needs to decide, so that the
    SMT solver gives each theory the same partition of interface equalities. *)
