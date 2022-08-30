(** E-node.

      An e-node is a node in the congruence closure that is contained
      in some equivalence classe).
      An equivalence class is a set of terms that are currently equal
      in the partial model built by the solver.
      The class is represented by a collection of nodes, one of which is
      distinguished and is called the "representative".

      All information pertaining to the whole equivalence class is stored
      in its representative's {!E_node.t}.

      When two classes become equal (are "merged"), one of the two
      representatives is picked as the representative of the new class.
      The new class contains the union of the two old classes' nodes.

      We also allow theories to store additional information in the
      representative. This information can be used when two classes are
      merged, to detect conflicts and solve equations à la Shostak.
  *)

open Types_

type t = Types_.e_node
(** An E-node.

        A value of type [t] points to a particular Term.t, but see
        {!find} to get the representative of the class. *)

include Sidekick_sigs.PRINT with type t := t

val term : t -> Term.t
(** Term contained in this equivalence class.
        If [is_root n], then [Term.t n] is the class' representative Term.t. *)

val equal : t -> t -> bool
(** Are two classes {b physically} equal? To check for
        logical equality, use [CC.E_node.equal (CC.find cc n1) (CC.find cc n2)]
        which checks for equality of representatives. *)

val hash : t -> int
(** An opaque hash of this E_node.t. *)

val is_root : t -> bool
(** Is the E_node.t a root (ie the representative of its class)?
        See {!find} to get the root. *)

val iter_class : t -> t Iter.t
(** Traverse the congruence class.
        Precondition: [is_root n] (see {!find} below) *)

val iter_parents : t -> t Iter.t
(** Traverse the parents of the class.
        Precondition: [is_root n] (see {!find} below) *)

val as_lit : t -> Lit.t option

val swap_next : t -> t -> unit
(** Swap the next pointer of each node. If their classes were disjoint,
    they are now unioned. *)

module Internal_ : sig
  val iter_class_ : t -> t Iter.t
  val make : Term.t -> t
end
