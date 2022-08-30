open Sidekick_core

val lemma_lra : Lit.t list -> Proof_term.t
(** List of literals [l1…ln] where [¬l1 /\ … /\ ¬ln] is LRA-unsat *)

