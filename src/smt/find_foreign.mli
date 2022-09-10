(** Find foreign variables.

  This module is a modular discoverer of foreign variables (and boolean terms).
  It should run after preprocessing of terms.
  *)

open Sidekick_core

module type ACTIONS = sig
  val declare_need_th_combination : Term.t -> unit
  (** Declare that this term is a foreign variable in some other subterm. *)

  val add_lit_for_bool_term : ?default_pol:bool -> Term.t -> unit
  (** Add the (boolean) term to the SAT solver *)
end

type actions = (module ACTIONS)
type t
type hook = actions -> is_sub:bool -> Term.t -> unit

val create : unit -> t

val add_hook : t -> hook -> unit
(** Register a hook to detect foreign subterms *)

val traverse_term : t -> actions -> Term.t -> unit
(** Traverse subterms of this term to detect foreign variables
    and boolean subterms. *)
