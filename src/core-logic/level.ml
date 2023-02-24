open Types_

type view = level_view =
  | L_zero
  | L_succ of level
  | L_var of string  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

and t = level = { l_view: level_view; mutable l_id: int }

let[@inline] view (self : t) : view = self.l_view
let[@inline] equal (a : t) (b : t) : bool = a == b
let[@inline] hash (a : t) : int = Hash.int a.l_id
let[@inline] compare a b : int = compare a.l_id b.l_id

(* hashconsing *)
module H_cons = Hashcons.Make (struct
  type nonrec t = t

  let equal (a : t) (b : t) : bool =
    a == b
    ||
    match view a, view b with
    | L_zero, L_zero -> true
    | L_succ a, L_succ b -> equal a b
    | L_var a, L_var b -> String.equal a b
    | L_imax (a1, a2), L_imax (b1, b2) | L_max (a1, a2), L_max (b1, b2) ->
      equal a1 b1 && equal a2 b2
    | (L_zero | L_succ _ | L_var _ | L_max _ | L_imax _), _ -> false

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

type store = { h_cons: H_cons.t }

module Store = struct
  type t = store

  let create () : store = { h_cons = H_cons.create ~size:64 () }
end

let make_ (self : store) (l_view : view) : t =
  let lvl = { l_view; l_id = -1 } in
  H_cons.hashcons self.h_cons lvl

let zero self : t = make_ self L_zero
let succ self t : t = make_ self (L_succ t)
let one self = succ self @@ zero self
let var self n : t = make_ self (L_var n)

let rec max self a b : t =
  if equal a b then
    a
  else (
    match view a, view b with
    | L_succ a', L_succ b' -> succ self (max self a' b')
    | L_zero, _ -> b
    | _, L_zero -> a
    | _ ->
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
