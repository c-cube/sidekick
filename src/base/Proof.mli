
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

type t
(** A container for the whole proof *)

type proof_step
(** A proof step in the trace.

    The proof will store all steps, and at the end when we find the empty clause
    we can filter them to keep only the relevant ones. *)

include Sidekick_core.PROOF
  with type t := t
   and type proof_step := proof_step
   and type lit = Lit.t
   and type term = Term.t

val lemma_lra : Lit.t Iter.t -> proof_rule

include Sidekick_th_data.PROOF
  with type proof := t
   and type proof_step := proof_step
   and type lit := Lit.t
   and type term := Term.t

include Sidekick_th_bool_static.PROOF
  with type proof := t
   and type proof_step := proof_step
   and type lit := Lit.t
   and type term := Term.t

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

