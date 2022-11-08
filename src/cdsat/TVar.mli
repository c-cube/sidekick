(** Variables.

  A variable is a term in the finite basis for CDSAT. It must be assigned
  a value before the solver can answer "sat".
*)

type t = private int
type var = t

type theory_view = ..
(** The theory-specific data *)

(** Store of variables *)
module Store : sig
  type t

  val tst : t -> Term.store

  val create : Term.store -> t
  (** Create a new store *)
end

module Vec_of : Vec_sig.S with type elt := t
(** Vector of variables *)

include Sidekick_sigs.EQ_ORD_HASH with type t := t

type store = Store.t

type reason =
  | Decide of { level: int }
  | Propagate of { level: int; hyps: Vec_of.t; proof: Sidekick_proof.step_id }

val get_of_term : store -> Term.t -> t option
(** Get variable from term, if already associated *)

val term : store -> t -> Term.t
(** Term for this variable *)

val has_value : store -> t -> bool
(** Does the variable have a value in the current assignment? *)

val level : store -> t -> int
(** Level of the current assignment, or [-1] *)

val value : store -> t -> Value.t option
(** Value in the current assignment *)

val bool_value : store -> t -> bool option
(** Value in the current assignment, as a boolean *)

val theory_view : store -> t -> theory_view
(** Theory-specific view of the variable *)

val assign : store -> t -> value:Value.t -> level:int -> reason:reason -> unit
val unassign : store -> t -> unit

val pop_new_var : store -> t option
(** Pop a new variable if any, or return [None] *)

val pp : store -> t Fmt.printer

module Tbl : CCHashtbl.S with type key = t
module Set : CCSet.S with type elt = t
module Map : CCMap.S with type key = t

(** A map optimized for dense storage.

  This is useful when most variables have an entry in the map. *)
module Dense_map (Elt : sig
  type t

  val create : unit -> t
end) : sig
  type elt = Elt.t
  type t

  val create : unit -> t
  val get : t -> var -> elt
  val set : t -> var -> elt -> unit
  val iter : t -> f:(var -> elt -> unit) -> unit
end

(**/**)

module Internal : sig
  val create : store -> Term.t -> theory_view:theory_view -> t
  (** Obtain a variable for this term. Fails if the term already maps
      to a variable. *)
end

(**/**)
