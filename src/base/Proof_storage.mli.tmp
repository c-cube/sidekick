(** Proof representation *)

open Base_types

(** Configuration of proofs *)
module Config : sig
  type t

  val pp : t Fmt.printer

  val default : t
  (** Default proof config, enabled *)

  val empty : t
  (** Disabled proof, without storage *)

  val enable : bool -> t -> t
  (** Enable/disable proof storage *)

  val store_in_memory : t -> t
  (** Store proof in memory *)

  val store_on_disk_at : string -> t -> t
  (** [store_on_disk_at file] stores temporary proof in file [file] *)

  val no_store : t -> t
end

(** {2 Main Proof API} *)

module Proof_trace : Sidekick_core.PROOF_TRACE

type t = Proof_trace.t
(** A container for the whole proof *)

type step_id = Proof_trace.A.step_id
type rule = Proof_trace.A.rule

module Rule_sat :
  Sidekick_core.SAT_PROOF_RULES
    with type rule = rule
     and type lit = Lit.t
     and type step_id = step_id

module Rule_core :
  Sidekick_core.PROOF_CORE
    with type rule = rule
     and type lit = Lit.t
     and type term = Term.t
     and type step_id = step_id

val lemma_lra : Lit.t Iter.t -> rule
val lemma_relax_to_lra : Lit.t Iter.t -> rule
val lemma_lia : Lit.t Iter.t -> rule

module Rule_data :
  Sidekick_th_data.PROOF_RULES
    with type rule = rule
     and type lit = Lit.t
     and type term = Term.t

module Rule_bool :
  Sidekick_th_bool_static.PROOF_RULES
    with type rule = rule
     and type lit = Lit.t
     and type term = Term.t

(** {2 Creation} *)

val create : ?config:Config.t -> unit -> t
(** Create new proof.
    @param config modifies the proof behavior *)

val empty : t
(** Empty proof, stores nothing *)

val disable : t -> unit
(** Disable proof, even if the config would enable it *)

(** {2 Use the proof} *)

val iter_steps_backward : t -> Proof_ser.Step.t Iter.t
(** Iterates on all the steps of the proof, from the end.

    This will yield nothing if the proof was disabled or used
    a dummy backend. *)

module Unsafe_ : sig
  val id_of_proof_step_ : step_id -> Proof_ser.ID.t
end
