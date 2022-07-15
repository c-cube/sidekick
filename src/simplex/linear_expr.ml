(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

module type COEFF = Linear_expr_intf.COEFF
module type VAR = Linear_expr_intf.VAR

module type S = Linear_expr_intf.S

type bool_op = Linear_expr_intf.bool_op = Leq | Geq | Lt | Gt | Eq | Neq

module Make(C : COEFF)(Var : VAR) = struct
  module C = C
  module Var_map = CCMap.Make(Var)
  module Var = Var

  type var = Var.t
  type subst = (Var.t -> C.t)

  (** Linear combination of variables. *)
  module Comb = struct
    (* A map from variables to their coefficient in the linear combination. *)
    type t = C.t Var_map.t

    let compare = Var_map.compare C.compare

    let empty = Var_map.empty

    let is_empty = Var_map.is_empty

    let monomial c x =
      if C.equal c C.zero then empty else Var_map.singleton x c

    let monomial1 x = Var_map.singleton x C.one

    let as_singleton m =
      if is_empty m then None
      else (
        let x, c = Var_map.choose m in
        if is_empty (Var_map.remove x m) then Some (c, x) else None
      )

    let add c x e =
      let c' = Var_map.get_or ~default:C.zero x e in
      let c' = C.(c + c') in
      if C.equal C.zero c' then Var_map.remove x e else Var_map.add x c' e

    let[@inline] map2 ~fr ~f a b =
      Var_map.merge_safe
        ~f:(fun _ rhs -> match rhs with
            | `Left x -> Some x
            | `Right x -> Some (fr x)
            | `Both (x,y) -> f x y)
        a b

    let[@inline] some_if_nzero x =
      if C.equal C.zero x then None else Some x

    let filter_map ~f m =
      Var_map.fold
        (fun x y m -> match f y with
           | None -> m
           | Some z -> Var_map.add x z m)
        m Var_map.empty

    module Infix = struct
      let (+) = map2 ~fr:(fun x->x) ~f:(fun a b -> some_if_nzero C.(a + b))
      let (-) = map2 ~fr:C.neg ~f:(fun a b -> some_if_nzero C.(a - b))
      let ( * ) q = filter_map ~f:(fun x -> some_if_nzero C.(x * q))
    end

    include Infix

    let iter = Var_map.iter

    let of_list l = List.fold_left (fun e (c,x) -> add c x e) empty l
    let to_list e = Var_map.bindings e |> List.rev_map CCPair.swap

    let to_map e = e
    let of_map e = Var_map.filter (fun _ c -> not (C.equal C.zero c)) e

    let pp_pair =
      Fmt.(pair ~sep:(return "@ * ") C.pp Var.pp)

    let pp out (e:t) =
      Fmt.(hovbox @@ list ~sep:(return "@ + ") pp_pair) out (to_list e)

    let eval (subst : subst) (e:t) : C.t =
      Var_map.fold
        (fun x c acc -> C.(acc + c * subst x))
        e C.zero
  end

  (** A linear arithmetic expression, composed of a combination of variables
      with coefficients and a constant offset. *)
  module Expr = struct
    type t = {
      const : C.t;
      comb : Comb.t
    }

    let[@inline] const e = e.const
    let[@inline] comb e = e.comb

    let compare e e' =
      CCOrd.(C.compare e.const e'.const
             <?> (Comb.compare, e.comb, e'.comb))

    let pp fmt e =
      Format.fprintf fmt "@[<hov>%a@ + %a" Comb.pp e.comb C.pp e.const

    let[@inline] make comb const : t = { comb; const; }

    let of_const = make Comb.empty
    let of_comb c = make c C.zero
    let monomial c x = of_comb (Comb.monomial c x)
    let monomial1 x = of_comb (Comb.monomial1 x)
    let of_list c l = make (Comb.of_list l) c
    let zero = of_const C.zero

    let is_zero e = C.equal C.zero e.const  && Comb.is_empty e.comb
    let is_const e = Comb.is_empty e.comb

    let map2 f g e e' = make (f e.comb e'.comb) (g e.const e'.const)

    module Infix = struct
      let (+) = map2 Comb.(+) C.(+)
      let (-) = map2 Comb.(-) C.(-)
      let ( * ) c e =
        if C.equal C.zero c
        then zero
        else make Comb.(c * e.comb) C.(c * e.const)
    end
    include Infix

    let eval subst e = C.(e.const + Comb.eval subst e.comb)
  end

  module Constr = struct
    type op = bool_op = Leq | Geq | Lt | Gt | Eq | Neq

    (** Constraints are expressions implicitly compared to zero. *)
    type t = {
      expr: Expr.t;
      op: op;
    }

    let compare c c' =
      CCOrd.(poly c.op c'.op
             <?> (Expr.compare, c.expr, c'.expr))

    let pp_op out o =
      Fmt.string out (match o with
        | Leq -> "=<" | Geq -> ">=" | Lt -> "<"
        | Gt -> ">" | Eq -> "=" | Neq -> "!=")

    let pp out c =
      Format.fprintf out "(@[%a@ %a 0@])"
        Expr.pp c.expr pp_op c.op

    let op t = t.op
    let expr t = t.expr

    let[@inline] of_expr expr op = { expr; op; }

    let make comb op const = of_expr (Expr.make comb (C.neg const)) op

    let geq e c = make e Geq c
    let leq e c = make e Leq c
    let gt e c = make e Gt c
    let lt e c = make e Lt c
    let eq e c = make e Eq c
    let neq e c = make e Neq c

    let geq0 e = of_expr e Geq
    let leq0 e = of_expr e Leq
    let gt0 e = of_expr e Gt
    let lt0 e = of_expr e Lt
    let eq0 e = of_expr e Eq
    let neq0 e = of_expr e Neq

    let[@inline] split {expr = {Expr.const; comb}; op} =
      comb, op, C.neg const

    let eval subst c =
      let v = Expr.eval subst c.expr in
      begin match c.op with
        | Leq -> C.compare v C.zero <= 0
        | Geq -> C.compare v C.zero >= 0
        | Lt -> C.compare v C.zero < 0
        | Gt -> C.compare v C.zero > 0
        | Eq -> C.compare v C.zero = 0
        | Neq -> C.compare v C.zero <> 0
      end
  end
end[@@inline]

