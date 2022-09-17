(** Models

    A model can be produced when the solver is found to be in a
    satisfiable state after a call to {!solve}. *)

open Sidekick_core

type t

val empty : t
val is_empty : t -> bool
val mem : t -> Term.t -> bool
val find : t -> Term.t -> Term.t option
val eval : t -> Term.t -> Term.t option
val add : Term.t -> Term.t -> t -> t
val keys : t -> Term.t Iter.t
val to_iter : t -> (Term.t * Term.t) Iter.t

include Sidekick_sigs.PRINT with type t := t
