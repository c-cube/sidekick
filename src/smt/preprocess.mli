(** Preprocessor

    The preprocessor turn mixed, raw literals (possibly simplified) into
    literals suitable for reasoning.
    Every literal undergoes preprocessing.
    Typically some clauses are also added to the solver on the side, and some
    subterms are found to be foreign variables.
*)

open Sigs

type t
(** Preprocessor *)

val create :
  ?stat:Stat.t ->
  proof:proof_trace ->
  cc:CC.t ->
  simplify:Simplify.t ->
  Term.store ->
  t

(** Actions given to preprocessor hooks *)
module type PREPROCESS_ACTS = sig
  val proof : proof_trace

  val mk_lit : ?sign:bool -> term -> lit
  (** [mk_lit t] creates a new literal for a boolean term [t]. *)

  val add_clause : lit list -> step_id -> unit
  (** pushes a new clause into the SAT solver. *)

  val add_lit : ?default_pol:bool -> lit -> unit
  (** Ensure the literal will be decided/handled by the SAT solver. *)
end

type preprocess_actions = (module PREPROCESS_ACTS)
(** Actions available to the preprocessor *)

type preprocess_hook =
  t ->
  is_sub:bool ->
  recurse:(term -> term) ->
  preprocess_actions ->
  term ->
  term option
(** Given a term, preprocess it.

    The idea is to add literals and clauses to help define the meaning of
    the term, if needed. For example for boolean formulas, clauses
    for their Tseitin encoding can be added, with the formula acting
    as its own proxy symbol; or a new symbol might be added.

    @param preprocess_actions actions available during preprocessing.
*)

val on_preprocess : t -> preprocess_hook -> unit
(** Add a hook that will be called when terms are preprocessed *)

val simplify_and_preproc_lit :
  t -> preprocess_actions -> lit -> lit * step_id option

val preprocess_clause :
  t -> preprocess_actions -> lit list -> step_id -> lit list * step_id

val preprocess_clause_array :
  t -> preprocess_actions -> lit array -> step_id -> lit array * step_id

val cc : t -> CC.t
