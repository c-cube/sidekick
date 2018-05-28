
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

module type STATE = sig
  type t

  val state : t

  val on_merge: t -> Equiv_class.t -> Equiv_class.t -> Explanation.t -> unit
  (** Called when two classes are merged *)

  val on_assert: t -> Lit.t -> unit
  (** Called when a literal becomes true *)

  val final_check: t -> Lit.t Sequence.t -> unit
  (** Final check, must be complete (i.e. must raise a conflict
      if the set of literals is not satisfiable) *)

  val mk_model : t -> Lit.t Sequence.t -> Model.t
  (** Make a model for this theory's terms *)
end


(** Runtime state of a theory, with all the operations it provides. *)
type state = (module STATE)

(** Unsatisfiable conjunction.
    Its negation will become a conflict clause *)
type conflict = Lit.t list

(** Actions available to a theory during its lifetime *)
module type ACTIONS = sig
  val on_backtrack: (unit -> unit) -> unit
  (** Register an action to do when we backtrack *)

  val raise_conflict: conflict -> 'a
  (** Give a conflict clause to the solver *)

  val propagate_eq: Term.t -> Term.t -> Lit.t list -> unit
  (** Propagate an equality [t = u] because [e] *)

  val propagate_distinct: Term.t list -> neq:Term.t -> Lit.t -> unit
  (** Propagate a [distinct l] because [e] (where [e = neq] *)

  val propagate: Lit.t -> Lit.t list -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val add_local_axiom: Lit.t IArray.t -> unit
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  val add_persistent_axiom: Lit.t IArray.t -> unit
  (** Add toplevel clause to the SAT solver. This clause will
      not be backtracked. *)

  val find: Term.t -> Equiv_class.t
  (** Find representative of this term *)

  val all_classes: Equiv_class.t Sequence.t
  (** All current equivalence classes
      (caution: linear in the number of terms existing in the solver) *)
end

type actions = (module ACTIONS)

type t = {
  name: string;
  make: Term.state -> actions -> state;
}

let make ~name ~make () : t = {name;make}

let make_st
  (type st)
    ?(on_merge=fun _ _ _ _ -> ())
    ?(on_assert=fun _ _ -> ())
    ?(mk_model=fun _ _ -> Model.empty)
    ~final_check
    ~st
    () : state =
  let module A = struct
    type nonrec t = st
    let state = st
    let on_merge = on_merge
    let on_assert = on_assert
    let final_check = final_check
    let mk_model = mk_model
  end in
  (module A : STATE)
