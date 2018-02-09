
(** Runtime state of a theory, with all the operations it provides.
    ['a] is the internal state *)
type state = State : {
  mutable st: 'a;
  on_merge: 'a -> Equiv_class.t -> Equiv_class.t -> Explanation.t -> unit;
  (** Called when two classes are merged *)

  on_assert: 'a -> Lit.t -> unit;
  (** Called when a literal becomes true *)

  final_check: 'a -> Lit.t Sequence.t -> unit;
  (** Final check, must be complete (i.e. must raise a conflict
      if the set of literals is not satisfiable) *)
} -> state

(** Unsatisfiable conjunction.
    Will be turned into a set of literals, whose negation becomes a
    conflict clause *)
type conflict = Explanation.t Bag.t

(** Actions available to a theory during its lifetime *)
type actions = {
  on_backtrack: (unit -> unit) -> unit;
  (** Register an action to do when we backtrack *)

  at_lvl_0: unit -> bool;
  (** Are we at level 0 of backtracking? *)

  raise_conflict: 'a. conflict -> 'a;
  (** Give a conflict clause to the solver *)

  propagate_eq: Term.t -> Term.t -> Explanation.t -> unit;
  (** Propagate an equality [t = u] because [e] *)

  propagate: Lit.t -> Explanation.t Bag.t -> unit;
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  case_split: Clause.t -> unit;
  (** Force the solver to case split on this clause.
      The clause will be removed upon backtracking. *)

  add_axiom: Clause.t -> unit;
  (** Add a persistent axiom to the SAT solver. This will not
      be backtracked *)

  find: Term.t -> Equiv_class.t;
  (** Find representative of this term *)

  all_classes: Equiv_class.t Sequence.t;
  (** All current equivalence classes
      (caution: linear in the number of terms existing in the solver) *)
}

type t = {
  name: string;
  make: Term.state -> actions -> state;
}

let make ~name ~make () : t = {name;make}

let make_st
    ?(on_merge=fun _ _ _ _ -> ())
    ?(on_assert=fun _ _ -> ())
    ~final_check
    ~st
    () : state =
  State { st; on_merge; on_assert; final_check }
