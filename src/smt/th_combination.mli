(** Delayed Theory Combination *)

open Sidekick_core

type t

val create : ?stat:Stat.t -> Term.store -> t

val add_term_needing_combination : t -> Term.t -> unit
(** [add_term_needing_combination self t] means that [t] occurs as a foreign
  variable in another term, so it is important that its theory, and the
  theory in which it occurs, agree on it being equal to other
  foreign terms. *)

val pop_new_lits : t -> Lit.t list
(** Get the new literals that the solver needs to decide, so that the
    SMT solver gives each theory the same partition of interface equalities. *)
