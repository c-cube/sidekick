(* This file is free software. See file "license" for more details. *)

(** Models

    A model is a solution to the satisfiability question, created by the
    SMT solver when it proves the formula to be {b satisfiable}.

    A model gives a value to each term of the original formula(s), in
    such a way that  the formula(s) is true when the term is replaced by its
    value.
*)

open Base_types

module Val_map : sig
  type key = Value.t list
  type 'a t
  val empty : 'a t
  val is_empty : _ t -> bool
  val cardinal : _ t -> int
  val find : key -> 'a t -> 'a option
  val add : key -> 'a -> 'a t -> 'a t
end

(** Model for function symbols.

    Function models are a finite map from argument tuples to values,
    accompanied with a default value that every other argument tuples
    map to. In other words, it's of the form:

    [lambda x y. if (x=vx1,y=vy1) then v1 else if … then … else vdefault]
*)
module Fun_interpretation : sig
  type t = {
    cases: Value.t Val_map.t;
    default: Value.t;
  }

  val default : t -> Value.t
  val cases_list : t -> (Value.t list * Value.t) list

  val make :
    default:Value.t ->
    (Value.t list * Value.t) list ->
    t
end

(** Model *)
type t = {
  values: Value.t Term.Map.t;
  funs: Fun_interpretation.t Fun.Map.t;
}

(** Empty model *)
val empty : t

val add : Term.t -> Value.t -> t -> t

val mem : Term.t -> t -> bool

val find : Term.t -> t -> Value.t option

val merge : t -> t -> t

val pp : t CCFormat.printer

(** [eval m t] tries to evaluate term [t] in the model.
    If it succeeds, the value is returned, otherwise [None] is. *)
val eval : t -> Term.t -> Value.t option
