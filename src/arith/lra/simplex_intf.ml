(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

(** {1 Modular and incremental implementation of the general simplex}. *)

(** The simplex is used as a decision procedure for linear rational arithmetic
    problems.

    More information can be found on the particular flavor of this
    implementation at https://gbury.eu/public/papers/stage-m2.pdf
*)

module type S = sig
  (** The given type of the variables *)
  type var

  (** A map on variables *)
  module Var_map : CCMap.S with type key = var

  (** Parameter required at the creation of the simplex *)
  type param

  type lit

  (** The type of a (possibly not solved) linear system *)
  type t

  (** An unsatisfiability explanation is a couple [(x, expr)]. If [expr] is the
      empty list, then there is a contradiction between two given bounds of [x].
      Else, the explanation is an equality [x = expr] that is valid
      (it can be derived from the original equations of the system) from which a
      bound can be deduced which contradicts an already given bound of the
      system. *)
  type cert = {
    cert_var: var;
    cert_expr: (Q.t * var) list;
  }

  (** Generic type returned when solving the simplex. A solution is a list of
      bindings that satisfies all the constraints inside the system. If the
      system is unsatisfiable, an explanation of type ['cert] is returned. *)
  type res =
    | Solution of Q.t Var_map.t
    | Unsatisfiable of cert

  (** {3 Simplex construction} *)

  (** The empty system.
      @param fresh the state for generating fresh variables on demand. *)
  val create : param -> t

  (** [add_eq s (x, eq)] adds the equation [x=eq] to [s] *)
  val add_eq : t -> var * (Q.t * var) list -> unit

  (** [add_bounds (x, lower, upper)] adds to [s]
      the bounds [lower] and [upper] for the given variable [x].
      If the bound is loose on one side
      (no upper bounds for instance), the values [Q.inf] and
      [Q.minus_inf] can be used. By default, in a system, all variables
      have no bounds, i.e have lower bound [Q.minus_inf] and upper bound
      [Q.inf].
      Optional parameters allow to make the the bounds strict. Defaults to false,
      so that bounds are large by default. *)
  val add_bounds : t ->
    ?strict_lower:bool -> ?strict_upper:bool ->
    ?lower_reason:lit -> ?upper_reason:lit ->
    var * Q.t * Q.t -> unit

  val add_lower_bound : t -> ?strict:bool -> reason:lit -> var -> Q.t -> unit

  val add_upper_bound : t -> ?strict:bool -> reason:lit -> var -> Q.t -> unit

  (** {3 Simplex solving} *)

  (** [solve s] solves the system [s] and returns a solution, if one exists.
      This function may change the internal representation of the system to
      that of an equivalent one
      (permutation of basic and non basic variables and pivot operation
      on the tableaux).
      *)
  val solve : t -> res

  val check_cert :
    t ->
    cert ->
    [`Ok of lit list | `Bad_bounds of string * string | `Diff_not_0 of Q.t Var_map.t]
  (** checks that the certificat indeed yields to a contradiction
      in the current state of the simplex.
      @return [`Ok unsat_core] if the certificate is valid. *)

  (* TODO: push/pop? at least on bounds *)

  val pp_cert : cert CCFormat.printer

  val pp_full_state : t CCFormat.printer

  (**/**)
  val check_invariants : t -> bool (* check that all invariants hold *)
  val matrix_pp_width : int ref (* horizontal filling when we print the matrix *)
  (**/**)
end

(* TODO: benchmark
   - copy current implem;
   - move random generator somewhere shared;
   - compare cur & old implem;
   - optimize (remove find_expr?))
*)

module type S_FULL = sig
  include S

  module L : Linear_expr_intf.S
    with type C.t = Q.t and type Var.t = var and type Var.lit = lit

  type op = Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  type constr = L.Constr.t

  val add_constr : t -> constr -> lit -> unit
  (** Add a constraint to a simplex state. *)
end
