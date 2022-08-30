(** A signature is a shallow term shape where immediate subterms
      are representative *)

open Sidekick_core.CC_view
open Types_

type t = signature

let equal (s1 : t) s2 : bool =
  let open CC_view in
  s1 == s2
  ||
  match s1, s2 with
  | Bool b1, Bool b2 -> b1 = b2
  | App_fun (f1, []), App_fun (f2, []) -> Const.equal f1 f2
  | App_fun (f1, l1), App_fun (f2, l2) ->
    Const.equal f1 f2 && CCList.equal E_node.equal l1 l2
  | App_ho (f1, a1), App_ho (f2, a2) -> E_node.equal f1 f2 && E_node.equal a1 a2
  | Not a, Not b -> E_node.equal a b
  | If (a1, b1, c1), If (a2, b2, c2) ->
    E_node.equal a1 a2 && E_node.equal b1 b2 && E_node.equal c1 c2
  | Eq (a1, b1), Eq (a2, b2) -> E_node.equal a1 a2 && E_node.equal b1 b2
  | Opaque u1, Opaque u2 -> E_node.equal u1 u2
  | (Bool _ | App_fun _ | App_ho _ | If _ | Eq _ | Opaque _ | Not _), _ -> false

let hash (s : t) : int =
  let module H = CCHash in
  match s with
  | Bool b -> H.combine2 10 (H.bool b)
  | App_fun (f, l) -> H.combine3 20 (Const.hash f) (H.list E_node.hash l)
  | App_ho (f, a) -> H.combine3 30 (E_node.hash f) (E_node.hash a)
  | Eq (a, b) -> H.combine3 40 (E_node.hash a) (E_node.hash b)
  | Opaque u -> H.combine2 50 (E_node.hash u)
  | If (a, b, c) ->
    H.combine4 60 (E_node.hash a) (E_node.hash b) (E_node.hash c)
  | Not u -> H.combine2 70 (E_node.hash u)

let[@inline never] pp out = function
  | Bool b -> Fmt.bool out b
  | App_fun (f, []) -> Const.pp out f
  | App_fun (f, l) ->
    Fmt.fprintf out "(@[%a@ %a@])" Const.pp f (Util.pp_list E_node.pp) l
  | App_ho (f, a) -> Fmt.fprintf out "(@[%a@ %a@])" E_node.pp f E_node.pp a
  | Opaque t -> E_node.pp out t
  | Not u -> Fmt.fprintf out "(@[not@ %a@])" E_node.pp u
  | Eq (a, b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" E_node.pp a E_node.pp b
  | If (a, b, c) ->
    Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" E_node.pp a E_node.pp b E_node.pp c
