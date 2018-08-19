
open Solver_types

(** {1 Equivalence Classes} *)

(** An equivalence class is a set of terms that are currently equal
    in the partial model built by the solver.
    The class is represented by a collection of nodes, one of which is
    distinguished and is called the "representative".

    All information pertaining to the whole equivalence class is stored
    in this representative's node.

    When two classes become equal (are "merged"), one of the two
    representatives is picked as the representative of the new class.
    The new class contains the union of the two old classes' nodes.

    We also allow theories to store additional information in the
    representative. This information can be used when two classes are
    merged, to detect conflicts and solve equations à la Shostak.
*)

type t = equiv_class
type payload = equiv_class_payload = ..

val field_is_active : Node_bits.field
(** The term is needed for evaluation. We must try to evaluate it
    or to find a value for it using the theory *)

val field_is_pending : Node_bits.field
(** true iff the node is in the [cc.pending] queue *)

val field_is_literal : Node_bits.field
(** This term is a boolean literal, subject to propagations *)

(** {2 basics} *)

val term : t -> term
val equal : t -> t -> bool
val hash : t -> int
val pp : t Fmt.printer
val payload : t -> payload list

(** {2 Helpers} *)

val make : term -> t
(** Make a new equivalence class whose representative is the given term *)

val payload_find: f:(payload -> 'a option) -> t -> 'a option

val payload_pred: f:(payload -> bool) -> t -> bool

val set_payload : ?can_erase:(payload -> bool) -> t -> payload -> unit
(** Add given payload
    @param can_erase if provided, checks whether an existing value
      is to be replaced instead of adding a new entry *)

val get_field : Node_bits.field -> t -> bool
val set_field : Node_bits.field -> bool -> t -> unit

module Tbl : CCHashtbl.S with type key = t

(**/**)
val dummy : t
(**/**)
