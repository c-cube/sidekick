open Types_

type const_view += Str of string

let ops : Const.ops =
  (module struct
    let pp out = function
      | Str s -> Fmt.string out s
      | _ -> assert false

    let equal a b =
      match a, b with
      | Str s1, Str s2 -> s1 = s2
      | _ -> false

    let hash = function
      | Str s -> CCHash.string s
      | _ -> assert false

    let opaque_to_cc _ = false
  end)

let make name ~ty : Const.t = Const.make (Str name) ops ~ty
