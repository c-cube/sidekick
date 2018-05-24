
module Clause : sig
  type t = Lit.t IArray.t
  val pp : t CCFormat.printer
end = struct
  type t = Lit.t IArray.t

  let pp out c =
    if IArray.length c = 0 then CCFormat.string out "false"
    else if IArray.length c = 1 then Lit.pp out (IArray.get c 0)
    else (
      Format.fprintf out "[@[<hv>%a@]]"
        (Util.pp_iarray ~sep:" ∨ " Lit.pp) c
    )
end

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
    Its negation will become a conflict clause *)
type conflict = Lit.Set.t

(** Actions available to a theory during its lifetime *)
type actions = {
  on_backtrack: (unit -> unit) -> unit;
  (** Register an action to do when we backtrack *)

  raise_conflict: 'a. conflict -> 'a;
  (** Give a conflict clause to the solver *)

  propagate_eq: Term.t -> Term.t -> Lit.Set.t -> unit;
  (** Propagate an equality [t = u] because [e] *)

  propagate_distinct: Term.t list -> neq:Term.t -> Lit.t -> unit;
  (** Propagate a [distinct l] because [e] (where [e = neq] *)

  propagate: Lit.t -> Lit.Set.t -> unit;
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  add_local_axiom: Lit.t IArray.t -> unit;
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  add_persistent_axiom: Lit.t IArray.t -> unit;
  (** Add toplevel clause to the SAT solver. This clause will
      not be backtracked. *)

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
