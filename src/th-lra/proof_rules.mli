open Sidekick_core
module Proof = Sidekick_proof

val lemma_lra : Lit.t list -> Proof.Pterm.t
(** List of literals [l1…ln] where [¬l1 /\ … /\ ¬ln] is LRA-unsat *)
