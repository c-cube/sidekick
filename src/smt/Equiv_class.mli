
open Solver_types

type t = cc_node
type repr = private t
type payload = cc_node_payload

val field_expanded : Node_bits.field
(** Term is expanded? *)

val field_has_expansion_lit : Node_bits.field
(** Upon expansion, does this term have a special literal [Lit_expanded t]
    that should be asserted? *)

val field_is_lit : Node_bits.field
(** Is this term a boolean literal? *)

val field_is_split : Node_bits.field
(** Did we perform case split (Split 1) on this term?
    This is only relevant for terms whose type is a datatype. *)

val field_add_level_0 : Node_bits.field
(** Is the corresponding term to be re-added upon backtracking,
    down to level 0? *)

(** {2 basics} *)

val term : t -> term
val equal : t -> t -> bool
val hash : t -> int
val pp : t Fmt.printer
val payload : t -> payload list

module Repr : sig
  type node = t
  type t = repr

  val term : t -> term
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer
  val payload : t -> payload list

  val parents : t -> node Bag.t
  val class_ : t -> node Bag.t
end

(** {2 Helpers} *)

val make : term -> t
(** Make a new equivalence class whose representative is the given term *)

val payload_find: f:(payload -> 'a option) -> t -> 'a option

val payload_pred: f:(payload -> bool) -> t -> bool

val set_payload : ?can_erase:(payload -> bool) -> t -> payload -> unit
(** Add given payload
    @param can_erase if provided, checks whether an existing value
      is to be replaced instead of adding a new entry *)

(**/**)
val dummy : t
val unsafe_repr_of_node : t -> repr
val unsafe_repr_seq_of_seq : t Sequence.t -> repr Sequence.t
(**/**)
