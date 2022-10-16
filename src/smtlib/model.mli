(** Models

    A model can be produced when the solver is found to be in a
    satisfiable state after a call to {!solve}. *)

open Sidekick_core

type t
type value = Term.t
type fun_ = Term.t

module TL_map : CCMap.S with type key = value list

val empty : t
val is_empty : t -> bool
val add_fun_entry : fun_ -> value list -> value -> t -> t
val get_fun_entry : fun_ -> value list -> t -> value option
val get_fun_entries : fun_ -> t -> value TL_map.t option
val iter_fun_entries : t -> (fun_ * value TL_map.t) Iter.t
val eval : Term.t -> t -> value option

include Sidekick_sigs.PRINT with type t := t
