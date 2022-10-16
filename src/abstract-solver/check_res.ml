(** Result of solving for the current set of clauses *)

type value = Term.t

type sat_result = {
  get_value: Term.t -> value option;  (** Value for this term *)
  iter_classes: (Term.t Iter.t * value) Iter.t;
      (** All equivalence classes in the congruence closure *)
  eval_lit: Lit.t -> bool option;  (** Evaluate literal *)
  iter_true_lits: Lit.t Iter.t;
      (** Iterate on literals that are true in the trail *)
}
(** Satisfiable *)

type unsat_result = {
  unsat_core: unit -> Lit.t Iter.t;
      (** Unsat core (subset of assumptions), or empty *)
  unsat_proof: unit -> Sidekick_proof.Step.id option;
      (** Proof step for the empty clause *)
}
(** Unsatisfiable *)

(** Result of calling "check" *)
type t =
  | Sat of sat_result
  | Unsat of unsat_result
  | Unknown of Unknown.t
      (** Unknown, obtained after a timeout, memory limit, etc. *)

let pp out (self : t) =
  match self with
  | Sat _ -> Fmt.string out "Sat"
  | Unsat _ -> Fmt.string out "Unsat"
  | Unknown u -> Fmt.fprintf out "Unknown(%a)" Unknown.pp u
