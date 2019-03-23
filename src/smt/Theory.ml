
module Th_clause : sig
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

(** Unsatisfiable conjunction.
    Its negation will become a conflict clause *)
type conflict = Lit.t list

module CC_eq_class = CC.N
module CC_expl = CC.Expl

(** Actions available to a theory during its lifetime *)
module type ACTIONS = sig
  val cc : CC.t

  val raise_conflict: conflict -> 'a
  (** Give a conflict clause to the solver *)

  val propagate: Lit.t -> (unit -> Lit.t list) -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val propagate_l: Lit.t -> Lit.t list -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val add_lit : Lit.t -> unit
  (** Add the given literal to the SAT solver, so it gets assigned
      a boolean value *)

  val add_local_axiom: Lit.t list -> unit
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  val add_persistent_axiom: Lit.t list -> unit
  (** Add toplevel clause to the SAT solver. This clause will
      not be backtracked. *)
end

type actions = (module ACTIONS)

module type S = sig
  type t

  val name : string
  (** Name of the theory *)

  val create : Term.state -> t
  (** Instantiate the theory's state *)

  val on_new_term : t -> actions -> Term.t -> unit
  (** Called when a new term is added *)

  val on_merge: t -> actions -> CC_eq_class.t -> CC_eq_class.t -> CC_expl.t -> unit
  (** Called when two classes are merged *)

  val partial_check : t -> actions -> Lit.t Iter.t -> unit
  (** Called when a literal becomes true *)

  val final_check: t -> actions -> Lit.t Iter.t -> unit
  (** Final check, must be complete (i.e. must raise a conflict
      if the set of literals is not satisfiable) *)

  val mk_model : t -> Lit.t Iter.t -> Model.t -> Model.t
  (** Make a model for this theory's terms *)

  val push_level : t -> unit

  val pop_levels : t -> int -> unit

  val cc_th : t -> CC.Theory.t list

  (**/**)
  val check_invariants : t -> unit
  (**/**)
end

type t = (module S)

type 'a t1 = (module S with type t = 'a)

let make
  (type st)
    ?(check_invariants=fun _ -> ())
    ?(on_new_term=fun _ _ _ -> ())
    ?(on_merge=fun _ _ _ _ _ -> ())
    ?(partial_check=fun _ _ _ -> ())
    ?(mk_model=fun _ _ m -> m)
    ?(push_level=fun _ -> ())
    ?(pop_levels=fun _ _ -> ())
    ?(cc_th=fun _->[])
    ~name
    ~final_check
    ~create
    () : t =
  let module A = struct
    type nonrec t = st
    let name = name
    let create = create
    let on_new_term = on_new_term
    let on_merge = on_merge
    let partial_check = partial_check
    let final_check = final_check
    let mk_model = mk_model
    let check_invariants = check_invariants
    let push_level = push_level
    let pop_levels = pop_levels
    let cc_th = cc_th
  end in
  (module A : S)
