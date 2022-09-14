(** Model Builder.

  This contains a partial model, in construction. It is accessible to every
  theory, so they can contribute partial values.

  TODO: seen values?
*)

open Sigs

type t

include Sidekick_sigs.PRINT with type t := t

val create : Term.store -> t
val mem : t -> Term.t -> bool

val require_eval : t -> Term.t -> unit
(** Require that this term gets a value. *)

val add : t -> ?subs:Term.t list -> Term.t -> value -> unit
(** Add a value to the model.
   @param subs if provided, these terms will be passed to {!require_eval}
   to ensure they map to a value. *)

val gensym : t -> pre:string -> ty:Term.t -> Term.t
(** New fresh constant *)

type eval_cache = Term.Internal_.cache

val eval : ?cache:eval_cache -> t -> Term.t -> value

val pop_required : t -> Term.t option
(** gives the next subterm that is required but has no value yet *)

val to_model : t -> Model.t
