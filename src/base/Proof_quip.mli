
(** Proofs of unsatisfiability exported in Quip

    Proofs are used in sidekick when the problem is found {b unsatisfiable}.
    A proof collects inferences made by the solver into a list of steps,
    each with its own kind of justification (e.g. "by congruence"),
    and outputs it in some kind of format.

    Currently we target {{: https://c-cube.github.io/quip-book/ } Quip}
    as an {b experimental} proof backend.
*)

open Base_types

type t
(** The state holding the whole proof. *)

val pp_debug : sharing:bool -> t Fmt.printer

val of_proof : Proof.t -> Proof.proof_step -> t

val output : out_channel -> t -> unit
