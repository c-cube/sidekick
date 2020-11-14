
(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

(** {1 Linear expressions interface} *)

(** {2 Coefficients}

    Coefficients are used in expressions. They usually
    are either rationals, or integers.
*)
module type COEFF = sig
  type t

  val equal : t -> t -> bool
  (** Equality on coefficients. *)

  val compare : t -> t -> int
  (** Comparison on coefficients. *)

  val pp : t Fmt.printer
  (** Printer for coefficients. *)

  val zero : t
  (** The zero coefficient. *)

  val one : t
  (** The one coefficient (to rule them all, :p). *)

  val neg : t -> t
  (** Unary negation *)

  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  (** Standard operations on coefficients. *)
end

(** {2 Variable interface}

    Standard interface for variables that are meant to be used
    in expressions.
*)
module type VAR = sig
  type t
  (** Variable type. *)

  val compare : t -> t -> int
  (** Standard comparison function on variables. *)

  val pp : t Fmt.printer
  (** Printer for variables. *)

  type lit

  val pp_lit : lit Fmt.printer
end

(** {2 Fresh variables}

    Standard interface for variables with an infinite number
    of 'fresh' variables. A 'fresh' variable should be distinct
    from any other.
*)
module type FRESH = sig
  type var
  (** The type of variables. *)

  type t
  (** A type of state for creating fresh variables. *)

  val copy : t -> t
  (** Copy state *)

  val fresh : t -> var
  (** Create a fresh variable using an existing variable as base.
      TODO: need some explaining, about the difference with {!create}. *)
end

(** {2 Generative Variable interface}

    Standard interface for variables that are meant to be used
    in expressions. Furthermore, fresh variables can be generated
    (which is useful to refactor and/or put problems in specific
    formats used by algorithms).
*)
module type VAR_GEN = sig
  include VAR

  (** Generate fresh variables on demand *)
  module Fresh : FRESH with type var := t
end

module type VAR_EXTENDED = sig
  type user_var (** original variables *)

  type t =
    | User of user_var
    | Internal of int

  include VAR_GEN with type t := t
end

type bool_op = Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

(** {2 Linear expressions & formulas} *)

(** Linear expressions & formulas.

    This modules defines linear expressions (which are linear
    combinations of variables), and linear constraints, where
    the value of a linear expressions is constrained.
*)
module type S = sig
  module C : COEFF
  (** Coeficients used. Can be integers as well as rationals. *)

  module Var : VAR
  (** Variables used in expressions. *)

  type var = Var.t
  (** The type of variables appearing in expressions. *)

  module Var_map : CCMap.S with type key = var
  (** Maps from variables, used for expressions as well as substitutions. *)

  type subst = C.t Var_map.t
  (** Type for substitutions. *)

  (** Combinations.

      This module defines linear combnations as mapping from variables
      to coefficients. This allows for very fast computations.
  *)
  module Comb : sig
    type t = private C.t Var_map.t
    (** The type of linear combinations. *)

    val compare : t -> t -> int
    (** Comparisons on linear combinations. *)

    val pp : t Fmt.printer
    (** Printer for linear combinations. *)

    val is_empty : t -> bool
    (** Is the given expression empty ?*)

    (** {5 Creation} *)

    val empty : t
    (** The empty linear combination. *)

    val monomial : C.t -> var -> t
    (** [monome n v] creates the linear combination [n * v] *)

    val monomial1 : var -> t
    (** [monome1 v] creates the linear combination [1 * v] *)

    val add : C.t -> var -> t -> t
    (** [add n v t] adds the monome [n * v] to the combination [t]. *)


    (** Infix operations on combinations

        This module defines usual operations on linear combinations,
        as infix operators to ease reading of complex computations. *)
    module Infix : sig
      val (+) : t -> t -> t
      (** Addition between combinations. *)

      val (-) : t -> t -> t
      (** Substraction between combinations. *)

      val ( * ) : C.t -> t -> t
      (** Multiplication by a constant. *)
    end
    include module type of Infix
    (** Include the previous module. *)

    val of_list : (C.t * var) list -> t

    val to_list : t -> (C.t * var) list
    (** Converters to and from lists of monomes. *)

    val of_map : C.t Var_map.t -> t

    val to_map : t -> C.t Var_map.t

    (** {5 Semantics} *)

    val eval : subst -> t -> C.t
    (** Evaluate a linear combination given a substitution for its variables.
        TODO: document potential exceptions raised ?*)
  end

  (** {2 Linear expressions.} *)

  (** Linear expressions represent linear arithmetic expressions as
      a linear combination and a constant.  *)
  module Expr : sig
    type t
    (** The type of linear expressions. *)

    val comb : t -> Comb.t
    val const : t -> C.t

    val is_zero : t -> bool

    val compare : t -> t -> int
    (** Standard comparison function on expressions. *)

    val pp : t Fmt.printer
    (** Standard printing function on expressions. *)

    val zero : t
    (** The expression [2]. *)

    val of_const : C.t -> t
    (** The constant expression. *)

    val of_comb : Comb.t -> t
    (** Combination without constant *)

    val of_list : C.t -> (C.t * Var.t) list -> t

    val make : Comb.t -> C.t -> t
    (** [make c n] makes the linear expression [c + n]. *)

    val monomial : C.t -> var -> t

    val monomial1 : var -> t

    (** Infix operations on expressions

        This module defines usual operations on linear expressions,
        as infix operators to ease reading of complex computations. *)
    module Infix : sig
      val (+) : t -> t -> t
      (** Addition between expressions. *)

      val (-) : t -> t -> t
      (** Substraction between expressions. *)

      val ( * ) : C.t -> t -> t
      (** Multiplication by a constant. *)
    end
    include module type of Infix
    (** Include the previous module. *)

    (** {5 Semantics} *)

    val eval : subst -> t -> C.t
    (** Evaluate a linear expression given a substitution for its variables.
        TODO: document potential exceptions raised ?*)
  end

  (** {2 Linear constraints.}

      Represents constraints on linear expressions. *)
  module Constr : sig
    type op = bool_op
    (** Arithmetic comparison operators. *)

    type t = {
      expr: Expr.t;
      op: op;
    }
    (** Linear constraints. Expressions are implicitly compared to zero. *)

    val compare : t -> t -> int
    (** Standard comparison function. *)

    val pp : t Fmt.printer
    (** Standard printing function. *)

    val of_expr : Expr.t -> bool_op -> t
    val make : Comb.t -> bool_op -> C.t -> t
    (** Create a constraint from a linear expression/combination and a constant. *)

    val geq : Comb.t -> C.t -> t
    val leq : Comb.t -> C.t -> t
    val gt: Comb.t -> C.t -> t
    val lt : Comb.t -> C.t -> t
    val eq : Comb.t -> C.t -> t
    val neq : Comb.t -> C.t -> t

    val geq0 : Expr.t -> t
    val leq0 : Expr.t -> t
    val gt0 : Expr.t -> t
    val lt0 : Expr.t -> t
    val eq0 : Expr.t -> t
    val neq0 : Expr.t -> t

    val op : t -> bool_op
    val expr : t -> Expr.t
    (** Extract the given part from a constraint. *)

    val split : t -> Comb.t * bool_op * C.t
    (** Split the linear combinations from the constant *)

    val eval : subst -> t -> bool
    (** Evaluate the given constraint under a substitution. *)
  end
end

