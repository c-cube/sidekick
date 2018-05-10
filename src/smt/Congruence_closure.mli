(** {2 Congruence Closure} *)

open Solver_types

type t
(** Global state of the congruence closure *)

type node = Equiv_class.t
(** Node in the congruence closure *)

type repr = Equiv_class.t
(** Node that is currently a representative *)

type actions = {
  on_backtrack:(unit -> unit) -> unit;
  (** Register a callback to be invoked upon backtracking below the current level *)

  on_merge:repr -> repr -> explanation -> unit;
  (** Call this when two classes are merged *)

  raise_conflict: 'a. Lit.Set.t -> 'a;
  (** Report a conflict *)

  (* FIXME: take a delayed Lit.Set.t? *)
  propagate: Lit.t -> Explanation.t Bag.t -> unit;
  (** Propagate a literal *)
}

val create :
  ?size:int ->
  actions:actions ->
  Term.state ->
  t
(** Create a new congruence closure.
    @param acts the actions available to the congruence closure
*)

val find : t -> node -> repr
(** Current representative *)

val same_class : t -> node -> node -> bool
(** Are these two classes the same in the current CC? *)

val union : t -> node -> node -> explanation -> unit
(** Merge the two equivalence classes. Will be undone on backtracking. *)

val mem : t -> term -> bool
(** Is the term properly added to the congruence closure? *)

val add : t -> term -> node
(** Add the term to the congruence closure, if not present already.
    Will be backtracked. *)

val add_seq : t -> term Sequence.t -> unit
(** Add a sequence of terms to the congruence closure *)

val all_classes : t -> repr Sequence.t
(** All current classes *)

val assert_lit : t -> Lit.t -> unit
(** Given a literal, assume it in the congruence closure and propagate
    its consequences. Will be backtracked. *)

val assert_eq : t -> term -> term -> explanation -> unit

val assert_distinct : t -> term list -> neq:term -> explanation -> unit
(** [assert_distinct l ~expl:u e] asserts all elements of [l] are distinct
    with explanation [e]
    precond: [u = distinct l] *)

val check : t -> unit

val final_check : t -> unit

val explain_eq_n : ?init:Lit.Set.t -> t -> node -> node -> Lit.Set.t
(** explain why the two nodes are equal *)

val explain_eq_t : ?init:Lit.Set.t -> t -> term -> term -> Lit.Set.t
(** explain why the two terms are equal *)

val explain_unfold_bag : ?init:Lit.Set.t -> t -> explanation Bag.t -> Lit.Set.t

val explain_unfold_seq : ?init:Lit.Set.t -> t -> explanation Sequence.t -> Lit.Set.t
(** Unfold those explanations into a complete set of
    literals implying them *)