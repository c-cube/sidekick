open Types_

type const_view += Str of string

let ops =
  let pp out = function
    | Str s -> Fmt.string out s
    | _ -> assert false
  in

  let equal a b =
    match a, b with
    | Str s1, Str s2 -> s1 = s2
    | _ -> false
  in

  let hash = function
    | Str s -> CCHash.string s
    | _ -> assert false
  in

  let ser _sink = function
    | Str s -> "c.str", Ser_value.string s
    | _ -> assert false
  in
  { Const.Ops.pp; equal; hash; ser }

let const_decoders : Const.decoders =
 fun _tst ->
  [
    ( "c.str",
      ops,
      fun _dec_term ->
        Ser_decode.(
          let+ s = string in
          Str s) );
  ]

let make name ~ty : Const.t = Const.make (Str name) ops ~ty
