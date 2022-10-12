(** Resolved explanations.

    The congruence closure keeps explanations for why terms are in the same
    class. However these are represented in a compact, cheap form.
    To use these explanations we need to {b resolve} them into a
    resolved explanation, typically a list of
    literals that are true in the current trail and are responsible for
    merges.

    However, we can also have merged classes because they have the same value
    in the current model. *)

open Types_

type t = { lits: Lit.t list; pr: Proof.Pterm.delayed }

include Sidekick_sigs.PRINT with type t := t
