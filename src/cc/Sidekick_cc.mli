(** Congruence Closure Implementation *)

open Sidekick_core
module View = View

module type ARG = Sigs.ARG

module type S = sig
  include Sigs.S

  val create :
    ?stat:Stat.t -> ?size:[ `Small | `Big ] -> Term.store -> Proof_trace.t -> t
  (** Create a new congruence closure.

      @param term_store used to be able to create new terms. All terms
      interacting with this congruence closure must belong in this term state
      as well. *)

  (**/**)

  module Debug_ : sig
    val pp : t Fmt.printer
    (** Print the whole CC *)
  end

  (**/**)
end

module Make (_ : ARG) : S
