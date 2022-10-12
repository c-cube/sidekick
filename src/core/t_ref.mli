(** Term reference *)

open Sidekick_core_logic

type t = Sidekick_trace.entry_id
(** Reference to another term, by a unique ID in a trace.

  This allows a trace to contain terms with explicit references
  to other terms, but where these references have to be followed explicitly.
  Thus, each term can be deserialized separately.

  For example, a proof term for a given lemma might use references to previous
  lemmas, instead of their direct proof terms; this allows a checker or
  proof GUI to only read this particular lemma's proof into a term.
*)

type Const.view += private Ref of t

val ref : Term.store -> t -> ty:Term.t -> Term.t
(** [ref tst id ~ty] is the reference to entry [id] in a trace,
    which must be
    a term of type [ty]. *)

val as_ref : Term.t -> t option
(** [as_ref (ref tst id ~ty)] is [Some id]. *)

val const_decoders : Const.decoders
