(** Proofs of unsatisfiability in the Quip proof format..

    This targets {{: https://c-cube.github.io/quip-book/ } Quip}
    as an {b experimental} proof backend.
*)

module Proof = Proof

type t = Proof.t
(** The state holding the whole proof. *)

(** What format to use to serialize the proof? *)
type out_format =
  | Sexp  (** S-expressions *)
  | CSexp  (** Canonical S-expressions *)

val pp_out_format : out_format Fmt.printer
val output : ?fmt:out_format -> out_channel -> t -> unit
val pp_debug : t Fmt.printer
