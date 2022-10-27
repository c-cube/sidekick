(** Variables.

  A variable is a term in the finite basis for CDSAT. It must be assigned
  a value before the solver can answer "sat".
*)

type t = private int
type var = t

(** Store of variables *)
module Store : sig
  type t

  val create : Term.store -> t
  (** Create a new store *)
end

module Vec_of : Vec_sig.S with type elt := t
(** Vector of variables *)

type store = Store.t

(** Reason for assignment *)
module Reason : sig
  type t =
    | Decide
    | Propagate of { level: int; hyps: Vec_of.t; proof: Sidekick_proof.step_id }

  include Sidekick_sigs.PRINT with type t := t

  val decide : t
  val propagate_v : store -> Vec_of.t -> Sidekick_proof.step_id -> t
  val propagate_l : store -> var list -> Sidekick_proof.step_id -> t
end

val of_term : store -> Term.t -> t
(** Obtain a variable for this term. *)

val term : store -> t -> Term.t
(** Term for this variable *)

val has_value : store -> t -> bool
(** Does the variable have a value in the current assignment? *)

val level : store -> t -> int
(** Level of the current assignment, or [-1] *)

val value : store -> t -> Value.t option
(** Value in the current assignment *)

val set_value : store -> t -> Value.t -> unit
val unset_value : store -> t -> unit

val watchers : store -> t -> t Vec.t
(** [watchers store t] is a vector of other variables watching [t],
    generally updated via {!Watch1} and {!Watch2}.
    These other variables are notified when [t] is assigned. *)

val add_watcher : store -> t -> watcher:t -> unit

val pop_new_var : store -> t option
(** Pop a new variable if any, or return [None] *)
