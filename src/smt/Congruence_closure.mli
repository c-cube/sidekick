(** {2 Congruence Closure} *)

open CDCL
open Solver_types

type t
(** Global state of the congruence closure *)

type node = Equiv_class.t
(** Node in the congruence closure *)

type repr = Equiv_class.repr
(** Node that is currently a representative *)

val create :
  ?size:int ->
  on_backtrack:((unit -> unit) -> unit) ->
  at_lvl_0:(unit -> bool) ->
  on_merge:(repr -> repr -> cc_explanation -> unit) list ->
  Term.state ->
  t
(** Create a new congruence closure.
    @param on_backtrack used to register undo actions
    @param on_merge callbacks called when two equiv classes are merged
*)

val find : t -> node -> repr
(** Current representative *)

val same_class : t -> node -> node -> bool
(** Are these two classes the same in the current CC? *)

val union : t -> node -> node -> cc_explanation -> unit
(** Merge the two equivalence classes. Will be undone on backtracking. *)

val assert_lit : t -> Lit.t -> unit
(** Given a literal, assume it in the congruence closure and propagate
    its consequences. Will be backtracked. *)

val mem : t -> term -> bool
(** Is the term properly added to the congruence closure? *)

val add : t -> term -> node
(** Add the term to the congruence closure, if not present already.
    Will be backtracked. *)

val add_seq : t -> term Sequence.t -> unit
(** Add a sequence of terms to the congruence closure *)

type actions =
  | Propagate of Lit.t * cc_explanation list
  | Split of Lit.t list * cc_explanation list
  | Merge of node * node (* merge these two classes *)

type result =
  | Sat of actions list
  | Unsat of cc_explanation list
  (* list of direct explanations to the conflict. *)

val check : t -> result

val final_check : t -> result

val explain_unfold: t -> cc_explanation list -> Lit.Set.t
(** Unfold those explanations into a complete set of
    literals implying them *)
