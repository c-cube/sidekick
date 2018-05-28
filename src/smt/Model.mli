
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

type t = {
  values: Value.t Term.Map.t;
}

val empty : t

val add : Term.t -> Value.t -> t -> t

val mem : Term.t -> t -> bool

val find : Term.t -> t -> Value.t option

val merge : t -> t -> t

val pp : t CCFormat.printer

val eval : t -> Term.t -> Value.t option
