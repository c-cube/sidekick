
(** Proofs of unsatisfiability in the Quip proof format..

    This targets {{: https://c-cube.github.io/quip-book/ } Quip}
    as an {b experimental} proof backend.
*)

type t
(** The state holding the whole proof. *)

val pp_debug : t Fmt.printer

val output : out_channel -> t -> unit
