(** Delayed Theory Combination *)

open Sidekick_core

type t

val create : ?stat:Stat.t -> Term.store -> t

val claim_term : t -> th_id:Theory_id.t -> Term.t -> unit
(** [claim_term self ~th_id t] means that theory with ID [th_id]
    claims the term [t].

    This means it might assert [t = u] or [t ≠ u] for some other term [u],
    or it might assign a value to [t] in the model in case of a SAT answer.
    That means it has to agree with other theories on what [t] is equal to.

    If a term is claimed by several theories, it will be eligible for theory
    combination.
*)

val pop_new_lits : t -> Lit.t list
(** Get the new literals that the solver needs to decide, so that the
    SMT solver gives each theory the same partition of interface equalities. *)
