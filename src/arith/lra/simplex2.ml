
(** {1 Fast Simplex for CDCL(T)}

    We follow the paper "Integrating Simplex with DPLL(T )" from
    de Moura and Dutertre.
*)

module type VAR = Linear_expr_intf.VAR

(** {2 Basic operator} *)
module Op = struct
  type t =
    | Leq
    | Lt
    | Geq
    | Gt

  let to_string = function
    | Leq -> "<="
    | Lt -> "<"
    | Geq -> ">="
    | Gt -> ">"
  let pp out op = Fmt.string out (to_string op)
end

module type S = sig
  module V : VAR

  type num = Q.t (** Numbers *)

  module Constraint : sig
    type op = Op.t

    (** A constraint is the comparison of a variable to a constant. *)
    type t = private {
      op: op;
      lhs: V.t;
      rhs: num;
    }

    val pp : t Fmt.printer
  end

  type t

  val create : unit -> t
  (** Create a new simplex. *)

  val define : t -> V.t -> (num * V.t) list -> unit
  (** Define a basic variable in terms of other variables.
      This is useful to "name" a linear expression and get back a variable
      that can be used in a {!Constraint.t} *)
end

module Make(Var: VAR)
  : S with module V = Var
= struct
  module V = Var

  type num = Q.t (** Numbers *)

  module Constraint = struct
    type op = Op.t

    (** A constraint is the comparison of a variable to a constant. *)
    type t = {
      op: op;
      lhs: V.t;
      rhs: num;
    }

    let pp out (self:t) =
      Fmt.fprintf out "(@[%a %s@ %a@])" V.pp self.lhs
        (Op.to_string self.op) Q.pp_print self.rhs
  end

  (** An extended rational, used to introduce ε so we can use strict
      comparisons in an algorithm designed to handle >= only.

      In a way, an extended rational is a tuple `(base, factor)`
      ordered lexicographically. *)
  type erat = {
    base: num; (** reference number *)
    eps_factor: num; (** coefficient for epsilon, the infinitesimal *)
  }

  (** {2 Epsilon-rationals, used for strict bounds} *)
  module Erat = struct
    type t = erat

    let zero : t = {base=Q.zero; eps_factor=Q.zero}

    let[@inline] make base eps_factor : t = {base; eps_factor}
    let[@inline] base t = t.base
    let[@inline] eps_factor t = t.eps_factor
    let[@inline] mul k e = make Q.(k * e.base) Q.(k * e.eps_factor)
    let[@inline] sum e1 e2 = make Q.(e1.base + e2.base) Q.(e1.eps_factor + e2.eps_factor)
    let[@inline] compare e1 e2 = match Q.compare e1.base e2.base with
      | 0 -> Q.compare e1.eps_factor e2.eps_factor
      | x -> x

    let[@inline] lt a b = compare a b < 0
    let[@inline] gt a b = compare a b > 0

    let[@inline] min x y = if compare x y <= 0 then x else y
    let[@inline] max x y = if compare x y >= 0 then x else y

    let[@inline] evaluate (epsilon:Q.t) (e:t) : Q.t = Q.(e.base + epsilon * e.eps_factor)

    let pp out e : unit =
      if Q.equal Q.zero (eps_factor e)
      then Q.pp_print out (base e)
      else
        Fmt.fprintf out "(@[<h>%a + @<1>ε * %a@])"
          Q.pp_print (base e) Q.pp_print (eps_factor e)
  end

  type t = unit

  let create () : t = ()

  let define _ = assert false (* TODO *)
end
