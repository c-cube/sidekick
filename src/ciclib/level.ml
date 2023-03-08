open Types_

type var = string

type t = level =
  | L_zero
  | L_succ of level
  | L_var of var  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

let rec equal (a : t) (b : t) : bool =
  match a, b with
  | L_zero, L_zero -> true
  | L_succ a, L_succ b -> equal a b
  | L_var a, L_var b -> String.equal a b
  | L_imax (a1, a2), L_imax (b1, b2) | L_max (a1, a2), L_max (b1, b2) ->
    equal a1 b1 && equal a2 b2
  | (L_zero | L_succ _ | L_var _ | L_max _ | L_imax _), _ -> false

let as_offset (self : t) : t * int =
  let rec loop n l =
    match l with
    | L_succ a -> loop (n + 1) a
    | _ -> l, n
  in
  loop 0 self

let rec pp out (self : t) : unit =
  let lvl, offset = as_offset self in
  let pp_offset out () = if offset > 0 then Fmt.fprintf out " + %d" offset in
  match lvl with
  | L_zero -> Fmt.int out offset
  | L_succ _ -> assert false
  | L_var v -> Fmt.fprintf out "%s%a" v pp_offset ()
  | L_max (a, b) -> Fmt.fprintf out "max(%a, %a)%a" pp a pp b pp_offset ()
  | L_imax (a, b) -> Fmt.fprintf out "imax(%a, %a)%a" pp a pp b pp_offset ()

let to_string = Fmt.to_string pp

let rec is_ground (l : t) : bool =
  match l with
  | L_zero -> true
  | L_succ a -> is_ground a
  | L_var _ -> false
  | L_max (a, b) | L_imax (a, b) -> is_ground a && is_ground b

let zero : t = L_zero
let[@inline] succ t : t = L_succ t
let one = succ zero
let[@inline] var n : t = L_var n

let rec max a b : t =
  if equal a b then
    a
  else (
    match a, b with
    | L_succ a', L_succ b' -> succ (max a' b')
    | L_zero, _ -> b
    | _, L_zero -> a
    | _ ->
      (* normalize wrt commutativity *)
      let a, b =
        if compare a b > 0 then
          b, a
        else
          a, b
      in
      L_max (a, b)
  )

let rec imax a b : t =
  if equal a b then
    a
  else (
    match a, b with
    | _, L_zero -> zero (* imax(_, 0) = 0 *)
    | L_succ a', L_succ b' -> succ (imax a' b')
    | _, L_succ _ -> max a b (* imax(, S_) is just max *)
    | L_zero, _ -> b
    | _ -> L_imax (a, b)
  )

let of_int i : t =
  assert (i >= 0);
  let rec loop i =
    if i = 0 then
      zero
    else
      succ @@ loop (i - 1)
  in
  loop i

let[@inline] is_zero l =
  match l with
  | L_zero -> true
  | _ -> false

type subst = t Util.Str_map.t

(** [subst_v store lvl v u] replaces [v] with [u] in [lvl] *)
let subst (subst : subst) (lvl : t) : t =
  let rec loop lvl : t =
    if is_ground lvl then
      lvl
    else (
      match lvl with
      | L_var v ->
        (match Util.Str_map.find v subst with
        | l -> l
        | exception Not_found -> lvl)
      | L_zero -> lvl
      | L_succ a -> succ (loop a)
      | L_max (a, b) -> max (loop a) (loop b)
      | L_imax (a, b) -> imax (loop a) (loop b)
    )
  in
  loop lvl

let subst_v (lvl : t) (v : string) (u : t) =
  subst (Util.Str_map.singleton v u) lvl

let is_one l =
  match l with
  | L_succ a -> is_zero a
  | _ -> false

let as_int self : _ option =
  let lvl, offset = as_offset self in
  if is_zero lvl then
    Some offset
  else
    None

let is_int self : bool = Option.is_some (as_int self)

let judge_leq l1 l2 : bool =
  (* [l <= l' + n] *)
  let rec prove (l : t) (l' : t) n : bool =
    (* replace [v] as [0] and [succ v], prove in both cases *)
    let split_on_var (v : string) =
      (let v' = zero in
       prove (subst_v l v v') (subst_v l' v v') n)
      &&
      let v' = succ (var v) in
      prove (subst_v l v v') (subst_v l' v v') n
    in

    match l, l' with
    | _ when equal l l' && n >= 0 -> true
    | L_zero, L_zero -> n >= 0
    | L_zero, _ when n >= 0 -> true
    | _, L_zero when n < 0 -> false
    | L_var v, L_var v' -> String.equal v v' && n >= 0
    | L_var _, L_zero -> false (* can instantiate var high enough to refute *)
    | L_zero, L_var _ -> n >= 0
    | L_succ l, _ -> prove l l' (n - 1)
    | _, L_succ l' -> prove l l' (n + 1)
    | _, L_max (l1, l2) -> prove l l1 n || prove l l2 n
    | L_max (l1, l2), _ -> prove l1 l' n && prove l2 l' n
    | L_imax (_, L_var v), _ | _, L_imax (_, L_var v) ->
      (* imax containing var? split *)
      split_on_var v
    | L_imax (l1, L_imax (l2, l3)), _ ->
      prove (max (imax l1 l3) (imax l2 l3)) l' n
    | _, L_imax (l1, L_imax (l2, l3)) ->
      prove l (max (imax l1 l3) (imax l2 l3)) n
    | L_imax (l1, L_max (l2, l3)), _ ->
      prove (max (imax l1 l2) (imax l1 l3)) l' n
    | _, L_imax (l1, L_max (l2, l3)) ->
      prove l (max (imax l1 l2) (imax l1 l3)) n
    | L_imax (_, (L_zero | L_succ _)), _ | _, L_imax (_, (L_zero | L_succ _)) ->
      assert false (* smart cstor makes this impossible *)
  in

  equal l1 l2
  ||
  let l2, n = as_offset l2 in
  prove l1 l2 n

let judge_eq l1 l2 : bool = equal l1 l2 || (judge_leq l1 l2 && judge_leq l2 l1)
let judge_is_zero l : bool = judge_leq l zero
let judge_is_nonzero l : bool = judge_leq one l
