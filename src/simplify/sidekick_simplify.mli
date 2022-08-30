(** Term simplifier *)

open Sidekick_core

type t

val tst : t -> Term.store

val create : Term.store -> proof:Proof_trace.t -> t
(** Create a simplifier *)

val clear : t -> unit
(** Reset internal cache, etc. *)

val proof : t -> Proof_trace.t
(** Access proof *)

type hook = t -> Term.t -> (Term.t * Proof_step.id Iter.t) option
(** Given a Term.t, try to simplify it. Return [None] if it didn't change.

    A simple example could be a hook that takes a Term.t [t],
    and if [t] is [app "+" (const x) (const y)] where [x] and [y] are number,
    returns [Some (const (x+y))], and [None] otherwise.

    The simplifier will take care of simplifying the resulting Term.t further,
    caching (so that work is not duplicated in subterms), etc.
*)

val add_hook : t -> hook -> unit

val normalize : t -> Term.t -> (Term.t * Proof_step.id) option
(** Normalize a Term.t using all the hooks. This performs
    a fixpoint, i.e. it only stops when no hook applies anywhere inside
    the Term.t. *)

val normalize_t : t -> Term.t -> Term.t * Proof_step.id option
(** Normalize a Term.t using all the hooks, along with a proof that the
    simplification is correct.
    returns [t, ø] if no simplification occurred. *)
