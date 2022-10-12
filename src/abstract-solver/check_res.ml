(** Result of solving for the current set of clauses *)

module Model = Sidekick_model

(** Result of calling "check" *)
type t =
  | Sat of Model.t  (** Satisfiable *)
  | Unsat of {
      unsat_core: unit -> Lit.t Iter.t;
          (** Unsat core (subset of assumptions), or empty *)
      unsat_step_id: unit -> Sidekick_proof.Step.id option;
          (** Proof step for the empty clause *)
    }  (** Unsatisfiable *)
  | Unknown of Unknown.t
      (** Unknown, obtained after a timeout, memory limit, etc. *)

let pp out (self : t) =
  match self with
  | Sat _ -> Fmt.string out "Sat"
  | Unsat _ -> Fmt.string out "Unsat"
  | Unknown u -> Fmt.fprintf out "Unknown(%a)" Unknown.pp u
