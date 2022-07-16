(** Main representation of Terms and Types *)
module type S = sig
  module Fun : Sidekick_sigs.EQ_HASH_PRINT
  (** A function symbol, like "f" or "plus" or "is_human" or "socrates" *)

  (** Types

      Types should be comparable (ideally, in O(1)), and have
      at least a boolean type available. *)
  module Ty : sig
    include Sidekick_sigs.EQ_HASH_PRINT

    type store

    val bool : store -> t
    val is_bool : t -> bool
  end

  (** Term structure.

      Terms should be {b hashconsed}, with perfect sharing.
      This allows, for example, {!Term.Tbl} and {!Term.iter_dag} to be efficient.
  *)
  module Term : sig
    include Sidekick_sigs.EQ_ORD_HASH_PRINT

    type store
    (** A store used to create new terms. It is where the hashconsing
        table should live, along with other all-terms related store. *)

    val ty : t -> Ty.t

    val bool : store -> bool -> t
    (** build true/false *)

    val as_bool : t -> bool option
    (** [as_bool t] is [Some true] if [t] is the term [true], and similarly
        for [false]. For other terms it is [None]. *)

    val abs : store -> t -> t * bool
    (** [abs t] returns an "absolute value" for the term, along with the
        sign of [t].

        The idea is that we want to turn [not a] into [(a, false)],
        or [(a != b)] into [(a=b, false)]. For terms without a negation this
        should return [(t, true)].

        The store is passed in case a new term needs to be created. *)

    val map_shallow : store -> (t -> t) -> t -> t
    (** Map function on immediate subterms. This should not be recursive. *)

    val iter_shallow : store -> (t -> unit) -> t -> unit
    (** Iterate function on immediate subterms. This should not be recursive. *)

    val iter_dag : t -> (t -> unit) -> unit
    (** [iter_dag t f] calls [f] once on each subterm of [t], [t] included.
        It must {b not} traverse [t] as a tree, but rather as a
        perfectly shared DAG.

        For example, in:
        {[
          let x = 2 in
          let y = f x x in
          let z = g y x in
          z = z
        ]}

        the DAG has the following nodes:

        {[ n1: 2
           n2: f n1 n1
           n3: g n2 n1
           n4: = n3 n3
         ]}
    *)

    module Tbl : CCHashtbl.S with type key = t
  end
end
