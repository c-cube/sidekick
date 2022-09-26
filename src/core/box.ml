open Sidekick_core_logic

type Const.view += Box of Term.t

let ops =
  let pp out = function
    | Box t -> Fmt.fprintf out "(@[box@ %a@])" Term.pp_debug t
    | _ -> assert false
  in

  let equal a b =
    match a, b with
    | Box a, Box b -> Term.equal a b
    | _ -> false
  in

  let hash = function
    | Box t -> Hash.(combine2 10 (Term.hash t))
    | _ -> assert false
  in

  let ser ser_t = function
    | Box t -> "box", ser_t t
    | _ -> assert false
  in
  { Const.Ops.pp; equal; hash; ser }

let const_decoders : Const.decoders =
 fun _tst ->
  [
    ( "box",
      ops,
      Ser_decode.(
        fun dec_t ->
          let+ t = dec_t in
          Box t) );
  ]

let as_box t =
  match Term.view t with
  | Term.E_const { Const.c_view = Box u; _ } -> Some u
  | _ -> None

let is_box t =
  match Term.view t with
  | Term.E_const { Const.c_view = Box _; _ } -> true
  | _ -> false

let box tst t : Term.t =
  match Term.view t with
  | Term.E_const { Const.c_view = _; _ } -> t
  | _ ->
    let c = Const.make (Box t) ~ty:(Term.ty t) ops in
    Term.const tst c
