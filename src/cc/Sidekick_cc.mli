(** Congruence Closure Implementation *)

module View = Sidekick_sigs_cc.View
open Sidekick_sigs_cc

module type ARG = ARG

module type S = sig
  include S

  val create :
    ?stat:Stat.t -> ?size:[ `Small | `Big ] -> term_store -> proof_trace -> t
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

module Make (A : ARG) :
  S
    with module T = A.T
     and module Lit = A.Lit
     and module Proof_trace = A.Proof_trace
