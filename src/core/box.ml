open Sidekick_core_logic

type Const.view += Box of Term.t

let ops : Const.ops =
  (module struct
    let pp out = function
      | Box t -> Fmt.fprintf out "(@[box@ %a@])" Term.pp_debug t
      | _ -> assert false

    let equal a b =
      match a, b with
      | Box a, Box b -> Term.equal a b
      | _ -> false

    let hash = function
      | Box t -> Hash.(combine2 10 (Term.hash t))
      | _ -> assert false

    let opaque_to_cc _ = false
  end)

let as_box t =
  match Term.view t with
  | Term.E_const { Const.c_view = Box u; _ } -> Some u
  | _ -> None

let box tst t : Term.t =
  match Term.view t with
  | Term.E_const { Const.c_view = Box _; _ } -> t
  | _ ->
    let c = Const.make (Box t) ~ty:(Term.ty t) ops in
    Term.const tst c
