(** {2 Congruence Closure} *)

open Solver_types

type t
(** Global state of the congruence closure *)

type node = Equiv_class.t
(** Node in the congruence closure *)

type repr = Equiv_class.t
(** Node that is currently a representative *)

type conflict = Theory.conflict

val create :
  ?on_merge:(repr -> repr -> explanation -> unit) ->
  ?size:[`Small | `Big] ->
  Term.state ->
  t
(** Create a new congruence closure.
    @param acts the actions available to the congruence closure
*)

val find : t -> node -> repr
(** Current representative *)

val add : t -> term -> node
(** Add the term to the congruence closure, if not present already.
    Will be backtracked. *)

val find_t : t -> term -> repr
(** Current representative of the term.
    @raise Not_found if the term is not already {!add}-ed. *)

val add_seq : t -> term Sequence.t -> unit
(** Add a sequence of terms to the congruence closure *)

val all_classes : t -> repr Sequence.t
(** All current classes *)

val assert_lit : t -> Lit.t -> unit
(** Given a literal, assume it in the congruence closure and propagate
    its consequences. Will be backtracked. *)

val assert_lits : t -> Lit.t Sequence.t -> unit

val assert_eq : t -> term -> term -> Lit.t list -> unit

val assert_distinct : t -> term list -> neq:term -> Lit.t -> unit
(** [assert_distinct l ~expl:u e] asserts all elements of [l] are distinct
    with explanation [e]
    precond: [u = distinct l] *)

val check : t -> sat_actions -> unit
(** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
    Will use the [sat_actions] to propagate literals, declare conflicts, etc. *)

val push_level : t -> unit

val pop_levels : t -> int -> unit

val mk_model : t -> Model.t -> Model.t
(** Enrich a model by mapping terms to their representative's value,
    if any. Otherwise map the representative to a fresh value *)

(**/**)
val check_invariants : t -> unit
val pp_full : t Fmt.printer
(**/**)
