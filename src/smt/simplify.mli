(** Term simplifier *)

open Sidekick_core
open Sigs

type t

val tst : t -> term_store

val clear : t -> unit
(** Reset internal cache, etc. *)

val proof : t -> proof_trace
(** Access proof *)

type hook = t -> term -> (term * step_id Iter.t) option
(** Given a term, try to simplify it. Return [None] if it didn't change.

        A simple example could be a hook that takes a term [t],
        and if [t] is [app "+" (const x) (const y)] where [x] and [y] are number,
        returns [Some (const (x+y))], and [None] otherwise.

        The simplifier will take care of simplifying the resulting term further,
        caching (so that work is not duplicated in subterms), etc.
    *)

val add_hook : t -> hook -> unit

val normalize : t -> term -> (term * step_id) option
(** Normalize a term using all the hooks. This performs
    a fixpoint, i.e. it only stops when no hook applies anywhere inside
    the term. *)

val normalize_t : t -> term -> term * step_id option
(** Normalize a term using all the hooks, along with a proof that the
    simplification is correct.
    returns [t, ø] if no simplification occurred. *)

val create : Term.store -> proof:Proof_trace.t -> t
