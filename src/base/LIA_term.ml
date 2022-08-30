open struct
  let hash_z = Z.hash
end

module LIA_pred = LRA_term.Pred
module LIA_op = LRA_term.Op

module LIA_view = struct
  type 'a t =
    | LRA_pred of LIA_pred.t * 'a * 'a
    | LRA_op of LIA_op.t * 'a * 'a
    | LRA_mult of Z.t * 'a
    | LRA_const of Z.t
    | LRA_other of 'a

  let map ~f_c f (l : _ t) : _ t =
    match l with
    | LRA_pred (p, a, b) -> LRA_pred (p, f a, f b)
    | LRA_op (p, a, b) -> LRA_op (p, f a, f b)
    | LRA_mult (n, a) -> LRA_mult (f_c n, f a)
    | LRA_const c -> LRA_const (f_c c)
    | LRA_other x -> LRA_other (f x)

  let iter f l : unit =
    match l with
    | LRA_pred (_, a, b) | LRA_op (_, a, b) ->
      f a;
      f b
    | LRA_mult (_, x) | LRA_other x -> f x
    | LRA_const _ -> ()

  let pp ~pp_t out = function
    | LRA_pred (p, a, b) ->
      Fmt.fprintf out "(@[%a@ %a@ %a@])" LRA_term.Pred.pp p pp_t a pp_t b
    | LRA_op (p, a, b) ->
      Fmt.fprintf out "(@[%a@ %a@ %a@])" LRA_term.Op.pp p pp_t a pp_t b
    | LRA_mult (n, x) -> Fmt.fprintf out "(@[*@ %a@ %a@])" Z.pp_print n pp_t x
    | LRA_const n -> Z.pp_print out n
    | LRA_other x -> pp_t out x

  let hash ~sub_hash = function
    | LRA_pred (p, a, b) ->
      Hash.combine4 81 (Hash.poly p) (sub_hash a) (sub_hash b)
    | LRA_op (p, a, b) ->
      Hash.combine4 82 (Hash.poly p) (sub_hash a) (sub_hash b)
    | LRA_mult (n, x) -> Hash.combine3 83 (hash_z n) (sub_hash x)
    | LRA_const n -> Hash.combine2 84 (hash_z n)
    | LRA_other x -> sub_hash x

  let equal ~sub_eq l1 l2 =
    match l1, l2 with
    | LRA_pred (p1, a1, b1), LRA_pred (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | LRA_op (p1, a1, b1), LRA_op (p2, a2, b2) ->
      p1 = p2 && sub_eq a1 a2 && sub_eq b1 b2
    | LRA_const a1, LRA_const a2 -> Z.equal a1 a2
    | LRA_mult (n1, x1), LRA_mult (n2, x2) -> Z.equal n1 n2 && sub_eq x1 x2
    | LRA_other x1, LRA_other x2 -> sub_eq x1 x2
    | (LRA_pred _ | LRA_op _ | LRA_const _ | LRA_mult _ | LRA_other _), _ ->
      false

  (* convert the whole structure to reals *)
  let to_lra f l : _ LRA_term.View.t =
    match l with
    | LRA_pred (p, a, b) -> LRA_term.View.LRA_pred (p, f a, f b)
    | LRA_op (op, a, b) -> LRA_term.View.LRA_op (op, f a, f b)
    | LRA_mult (c, x) -> LRA_term.View.LRA_mult (Q.of_bigint c, f x)
    | LRA_const x -> LRA_term.View.LRA_const (Q.of_bigint x)
    | LRA_other v -> LRA_term.View.LRA_other (f v)
end
