(** Fresh symbol generation *)

open Sidekick_core_logic

type term = Term.t
type ty = Term.t

type t
(** Fresh symbol generator.

      The theory needs to be able to create new terms with fresh names,
      to be used as placeholders for complex formulas during Tseitin
      encoding. *)

val create : Term.store -> t
(** New (stateful) generator instance. *)

val fresh_term : ?opaque_to_cc:bool -> t -> pre:string -> ty -> term
(** Make a fresh term of the given type *)
