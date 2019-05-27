
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

module Val_map : sig
  type key = Value.t list
  type 'a t
  val empty : 'a t
  val is_empty : _ t -> bool
  val cardinal : _ t -> int
  val find : key -> 'a t -> 'a option
  val add : key -> 'a -> 'a t -> 'a t
end

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

type t = {
  values: Value.t Term.Map.t;
  funs: Fun_interpretation.t Cst.Map.t;
}

val empty : t

val add : Term.t -> Value.t -> t -> t

val mem : Term.t -> t -> bool

val find : Term.t -> t -> Value.t option

val merge : t -> t -> t

val pp : t CCFormat.printer

val eval : t -> Term.t -> Value.t option
