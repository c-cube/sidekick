
(* This file is free software. See file "license" for more details. *)

(** {1 Solver}

    The solving algorithm, based on MCSat *)

module Sat_solver : Sidekick_sat.S
      with type formula = Lit.t
       and type theory = Theory_combine.t
       and type lemma = Theory_combine.proof

(** {2 Result} *)

type model = Model.t

module Proof : sig
  type t = Sat_solver.Proof.t

  val pp : t CCFormat.printer
end

type unknown =
  | U_timeout
  | U_max_depth
  | U_incomplete

type res =
  | Sat of Model.t
  | Unsat of Proof.t
  | Unknown of unknown

(** {2 Main} *)

type t
(** Solver state *)

val create :
  ?size:[`Big | `Tiny | `Small] ->
  ?config:Config.t ->
  theories:Theory.t list ->
  unit -> t

val solver : t -> Sat_solver.t
val th_combine : t -> Theory_combine.t
val add_theory : t -> Theory.t -> unit
val cc : t -> Congruence_closure.t
val stats : t -> Stat.t
val tst : t -> Term.state

val assume : t -> Lit.t IArray.t -> unit

val assume_eq : t -> Term.t -> Term.t -> Lit.t -> unit
val assume_distinct : t -> Term.t list -> neq:Term.t -> Lit.t -> unit

val solve :
  ?on_exit:(unit -> unit) list ->
  ?check:bool ->
  assumptions:Lit.t list ->
  t ->
  res
(** [solve s] checks the satisfiability of the statement added so far to [s]
    @param check if true, the model is checked before returning
    @param on_exit functions to be run before this returns *)

val pp_term_graph: t CCFormat.printer
val pp_stats : t CCFormat.printer
val pp_unknown : unknown CCFormat.printer
