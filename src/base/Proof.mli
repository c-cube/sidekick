(** Proofs of unsatisfiability

    Proofs are used in sidekick when the problem is found {b unsatisfiable}.
    A proof collects inferences made by the solver into a list of steps,
    each with its own kind of justification (e.g. "by congruence"),
    and outputs it in some kind of format.

    Currently we target {{: https://c-cube.github.io/quip-book/ } Quip}
    as an experimental proof backend.
*)

open Base_types

include Sidekick_core.PROOF
  with type term = Term.t
   and type ty = Ty.t

val isa_split : ty -> term Iter.t -> t
val isa_disj : ty -> term -> term -> t
val cstor_inj : Cstor.t -> int -> term list -> term list -> t

val bool_eq : term -> term -> t
val bool_c : string -> term list -> t
val ite_true : term -> t
val ite_false : term -> t

val lra : lit Iter.t -> t
val lra_l : lit list -> t

type out_format = Sexp | CSexp

type config = {
  self_contained: bool;
  (** Add all required type declarations and definitions to the proof *)

  flat: bool;
  (** If true, use many toplevel S-exprs as opposed to a single `(quip 1 …)` *)

  sharing: bool;
  (** Introduce sharing of terms to make the proof more compact? *)

  out_format: out_format;
  (** Format in which to print the proof *)
}

val default_config : config
val config_from_env : unit -> config
val pp_config : config Fmt.printer

module Quip : sig
  val output : config:config -> out_channel -> t -> unit
  (** Printer in Quip format (experimental) *)
end
