open Types_

type view = level_view =
  | L_zero
  | L_succ of level
  | L_var of string  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

and t = level = { l_view: level_view; mutable l_id: int; mutable l_flags: int }

let[@inline] view (self : t) : view = self.l_view
let[@inline] equal (a : t) (b : t) : bool = a == b
let[@inline] hash (a : t) : int = Hash.int a.l_id
let[@inline] compare a b : int = compare a.l_id b.l_id

let equal_view (a : view) (b : view) : bool =
  match a, b with
  | L_zero, L_zero -> true
  | L_succ a, L_succ b -> equal a b
  | L_var a, L_var b -> String.equal a b
  | L_imax (a1, a2), L_imax (b1, b2) | L_max (a1, a2), L_max (b1, b2) ->
    equal a1 b1 && equal a2 b2
  | (L_zero | L_succ _ | L_var _ | L_max _ | L_imax _), _ -> false

(* hashconsing *)
module H_cons = Hashcons.Make (struct
  type nonrec t = t

  let[@inline] equal a b = a == b || equal_view (view a) (view b)

  let hash a : int =
    match view a with
    | L_zero -> Hash.int 1
    | L_succ a -> Hash.combine2 2 (hash a)
    | L_var v -> Hash.combine2 3 (Hash.string v)
    | L_max (a, b) -> Hash.combine3 10 (hash a) (hash b)
    | L_imax (a, b) -> Hash.combine3 20 (hash a) (hash b)

  let set_id self i =
    assert (self.l_id = -1);
    self.l_id <- i
end)

let as_offset (self : t) : t * int =
  let rec loop n l =
    match view l with
    | L_succ a -> loop (n + 1) a
    | _ -> l, n
  in
  loop 0 self

let rec pp out (self : t) : unit =
  let lvl, offset = as_offset self in
  let pp_offset out () = if offset > 0 then Fmt.fprintf out " + %d" offset in
  match view lvl with
  | L_zero -> Fmt.int out offset
  | L_succ _ -> assert false
  | L_var v -> Fmt.fprintf out "%s%a" v pp_offset ()
  | L_max (a, b) -> Fmt.fprintf out "max(%a, %a)%a" pp a pp b pp_offset ()
  | L_imax (a, b) -> Fmt.fprintf out "imax(%a, %a)%a" pp a pp b pp_offset ()

let to_string = Fmt.to_string pp

(* 5 bits in [t.id] are used to store which store it belongs to, so we have
   a chance of detecting when the user passes a term to the wrong store *)
let store_id_bits = 5
let store_id_mask = (1 lsl store_id_bits) - 1

type store = { h_cons: H_cons.t; id: int }

module Store = struct
  type t = store

  let _id = ref 0

  let create () : store =
    let id = !_id land store_id_mask in
    incr _id;
    { h_cons = H_cons.create ~size:64 (); id }
end

let[@inline] is_ground (self : t) : bool = self.l_flags lsl store_id_bits != 0

let is_ground_view_ (view : view) : bool =
  match view with
  | L_zero -> true
  | L_succ a -> is_ground a
  | L_var _ -> false
  | L_max (a, b) | L_imax (a, b) -> is_ground a && is_ground b

let make_ (self : store) (l_view : view) : t =
  let lvl = { l_view; l_id = -1; l_flags = 0 } in
  let lvl' = H_cons.hashcons self.h_cons lvl in
  if lvl == lvl' then (
    let ground = is_ground_view_ l_view in
    lvl.l_flags <-
      (Util.int_of_bool ground lsl store_id_bits)
      lor (lvl.l_id lsl store_id_bits)
  );
  lvl'

let[@inline] zero self : t = make_ self L_zero
let[@inline] succ self t : t = make_ self (L_succ t)
let[@inline] one self = succ self @@ zero self
let[@inline] var self n : t = make_ self (L_var n)
let[@inline] store_id (self : t) : int = self.l_flags land store_id_mask

let rec max self a b : t =
  if equal a b then
    a
  else (
    match view a, view b with
    | L_succ a', L_succ b' -> succ self (max self a' b')
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
      make_ self (L_max (a, b))
  )

let rec imax self a b : t =
  if equal a b then
    a
  else (
    match view a, view b with
    | _, L_zero -> zero self (* imax(_, 0) = 0 *)
    | L_succ a', L_succ b' -> succ self (imax self a' b')
    | _, L_succ _ -> max self a b (* imax(, S_) is just max *)
    | L_zero, _ -> b
    | _ -> make_ self (L_imax (a, b))
  )

let of_int self i : t =
  assert (i >= 0);
  let rec loop i =
    if i = 0 then
      zero self
    else
      succ self @@ loop (i - 1)
  in
  loop i

let[@inline] is_zero l =
  match view l with
  | L_zero -> true
  | _ -> false

(** [subst_v store lvl v u] replaces [v] with [u] in [lvl] *)
let subst_v (self : store) (lvl : t) (v : string) (u : t) =
  let rec loop lvl : t =
    if is_ground lvl then
      lvl
    else (
      match view lvl with
      | L_var v' when v = v' -> u
      | L_var _ -> lvl
      | L_zero -> assert false
      | L_succ a -> succ self (loop a)
      | L_max (a, b) -> max self (loop a) (loop b)
      | L_imax (a, b) -> imax self (loop a) (loop b)
    )
  in
  loop lvl

let is_one l =
  match view l with
  | L_succ a -> is_zero a
  | _ -> false

let as_int self : _ option =
  let lvl, offset = as_offset self in
  if is_zero lvl then
    Some offset
  else
    None

let is_int self : bool = Option.is_some (as_int self)

let judge_leq st l1 l2 : bool =
  assert (store_id l1 = st.id);
  assert (store_id l2 = st.id);

  (* [l <= l' + n] *)
  let rec prove (l : t) (l' : t) n : bool =
    (* replace [v] as [0] and [succ v], prove in both cases *)
    let split_on_var (v : string) =
      (let v' = zero st in
       prove (subst_v st l v v') (subst_v st l' v v') n)
      &&
      let v' = succ st (var st v) in
      prove (subst_v st l v v') (subst_v st l' v v') n
    in

    match l.l_view, l'.l_view with
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
    | L_imax (_, { l_view = L_var v; _ }), _
    | _, L_imax (_, { l_view = L_var v; _ }) ->
      (* imax containing var? split *)
      split_on_var v
    | L_imax (l1, { l_view = L_imax (l2, l3); _ }), _ ->
      prove (max st (imax st l1 l3) (imax st l2 l3)) l' n
    | _, L_imax (l1, { l_view = L_imax (l2, l3); _ }) ->
      prove l (max st (imax st l1 l3) (imax st l2 l3)) n
    | L_imax (l1, { l_view = L_max (l2, l3); _ }), _ ->
      prove (max st (imax st l1 l2) (imax st l1 l3)) l' n
    | _, L_imax (l1, { l_view = L_max (l2, l3); _ }) ->
      prove l (max st (imax st l1 l2) (imax st l1 l3)) n
    | L_imax (_, { l_view = L_zero | L_succ _; _ }), _
    | _, L_imax (_, { l_view = L_zero | L_succ _; _ }) ->
      assert false (* smart cstor makes this impossible *)
  in

  equal l1 l2
  ||
  let l2, n = as_offset l2 in
  prove l1 l2 n

let judge_eq st l1 l2 : bool =
  equal l1 l2 || (judge_leq st l1 l2 && judge_leq st l2 l1)

let judge_is_zero st l : bool = judge_leq st l (zero st)
let judge_is_nonzero st l : bool = judge_leq st (one st) l
