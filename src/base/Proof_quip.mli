(** Export to Quip from {!module:Proof}.

    We use {!Sidekick_quip} but do not export anything from it. *)

type t

val of_proof : Proof.t -> unsat:Proof.proof_step -> t

type out_format = Sidekick_quip.out_format = Sexp | CSexp

val output : ?fmt:out_format -> out_channel -> t -> unit
