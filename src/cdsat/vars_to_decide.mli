(** Set of variables yet to decide *)

type t

val create : unit -> t
val mem : t -> TVar.t -> bool
val size : t -> int

val add : t -> TVar.t -> unit
(** Add a variable to the set *)

val bump : t -> TVar.t -> unit
(** [bump set v] makes [v] more likely to be decided sooner than later. *)

val pop_next : t -> TVar.t option
(** Pop next variable *)

val remove : t -> TVar.t -> unit
(** Remove the variable from the set *)
