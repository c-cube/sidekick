open struct
  let hash_z = Z.hash
  let[@inline] hash_q q = CCHash.combine2 (hash_z (Q.num q)) (hash_z (Q.den q))
end

module LRA_pred = struct
  type t = Sidekick_th_lra.Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  let to_string = function
    | Lt -> "<"
    | Leq -> "<="
    | Neq -> "!="
    | Eq -> "="
    | Gt -> ">"
    | Geq -> ">="

  let pp out p = Fmt.string out (to_string p)
end

module LRA_op = struct
  type t = Sidekick_th_lra.op = Plus | Minus

  let to_string = function
    | Plus -> "+"
    | Minus -> "-"

  let pp out p = Fmt.string out (to_string p)
end

module LRA_view = struct
  type 'a t =
    | Pred of LRA_pred.t * 'a * 'a
    | Op of LRA_op.t * 'a * 'a
    | Mult of Q.t * 'a
    | Const of Q.t
    | Var of 'a
    | To_real of 'a

  let map ~f_c f (l : _ t) : _ t =
    match l with
    | Pred (p, a, b) -> Pred (p, f a, f b)
    | Op (p, a, b) -> Op (p, f a, f b)
    | Mult (n, a) -> Mult (f_c n, f a)
    | Const c -> Const (f_c c)
    | Var x -> Var (f x)
    | To_real x -> To_real (f x)

  let iter f l : unit =
    match l with
    | Pred (_, a, b) | Op (_, a, b) ->
      f a;
      f b
    | Mult (_, x) | Var x | To_real x -> f x
    | Const _ -> ()

  let pp ~pp_t out = function
    | Pred (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_pred.to_string p) pp_t a pp_t b
    | Op (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_op.to_string p) pp_t a pp_t b
    | Mult (n, x) -> Fmt.fprintf out "(@[*@ %a@ %a@])" Q.pp_print n pp_t x
    | Const q -> Q.pp_print out q
    | Var x -> pp_t out x
    | To_real x -> Fmt.fprintf out "(@[to_real@ %a@])" pp_t x

  let hash ~sub_hash = function
    | Pred (p, a, b) -> Hash.combine4 81 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Op (p, a, b) -> Hash.combine4 82 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Mult (n, x) -> Hash.combine3 83 (hash_q n) (sub_hash x)
    | Const q -> Hash.combine2 84 (hash_q q)
    | Var x -> sub_hash x
    | To_real x -> Hash.combine2 85 (sub_hash x)

  let equal ~sub_eq l1 l2 =
    match l1, l2 with
    | Pred (p1, a1, b1), Pred (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Op (p1, a1, b1), Op (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Const a1, Const a2 -> Q.equal a1 a2
    | Mult (n1, x1), Mult (n2, x2) -> Q.equal n1 n2 && sub_eq x1 x2
    | Var x1, Var x2 | To_real x1, To_real x2 -> sub_eq x1 x2
    | (Pred _ | Op _ | Const _ | Mult _ | Var _ | To_real _), _ -> false
end

module LIA_pred = LRA_pred
module LIA_op = LRA_op

module LIA_view = struct
  type 'a t =
    | Pred of LIA_pred.t * 'a * 'a
    | Op of LIA_op.t * 'a * 'a
    | Mult of Z.t * 'a
    | Const of Z.t
    | Var of 'a

  let map ~f_c f (l : _ t) : _ t =
    match l with
    | Pred (p, a, b) -> Pred (p, f a, f b)
    | Op (p, a, b) -> Op (p, f a, f b)
    | Mult (n, a) -> Mult (f_c n, f a)
    | Const c -> Const (f_c c)
    | Var x -> Var (f x)

  let iter f l : unit =
    match l with
    | Pred (_, a, b) | Op (_, a, b) ->
      f a;
      f b
    | Mult (_, x) | Var x -> f x
    | Const _ -> ()

  let pp ~pp_t out = function
    | Pred (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_pred.to_string p) pp_t a pp_t b
    | Op (p, a, b) ->
      Fmt.fprintf out "(@[%s@ %a@ %a@])" (LRA_op.to_string p) pp_t a pp_t b
    | Mult (n, x) -> Fmt.fprintf out "(@[*@ %a@ %a@])" Z.pp_print n pp_t x
    | Const n -> Z.pp_print out n
    | Var x -> pp_t out x

  let hash ~sub_hash = function
    | Pred (p, a, b) -> Hash.combine4 81 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Op (p, a, b) -> Hash.combine4 82 (Hash.poly p) (sub_hash a) (sub_hash b)
    | Mult (n, x) -> Hash.combine3 83 (hash_z n) (sub_hash x)
    | Const n -> Hash.combine2 84 (hash_z n)
    | Var x -> sub_hash x

  let equal ~sub_eq l1 l2 =
    match l1, l2 with
    | Pred (p1, a1, b1), Pred (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Op (p1, a1, b1), Op (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | Const a1, Const a2 -> Z.equal a1 a2
    | Mult (n1, x1), Mult (n2, x2) -> Z.equal n1 n2 && sub_eq x1 x2
    | Var x1, Var x2 -> sub_eq x1 x2
    | (Pred _ | Op _ | Const _ | Mult _ | Var _), _ -> false

  (* convert the whole structure to reals *)
  let to_lra f l : _ LRA_view.t =
    match l with
    | Pred (p, a, b) -> LRA_view.Pred (p, f a, f b)
    | Op (op, a, b) -> LRA_view.Op (op, f a, f b)
    | Mult (c, x) -> LRA_view.Mult (Q.of_bigint c, f x)
    | Const x -> LRA_view.Const (Q.of_bigint x)
    | Var v -> LRA_view.Var (f v)
end
