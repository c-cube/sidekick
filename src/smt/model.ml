open Sigs

type t = Empty | Map of term Term.Tbl.t

let empty = Empty

let mem = function
  | Empty -> fun _ -> false
  | Map tbl -> Term.Tbl.mem tbl

let find = function
  | Empty -> fun _ -> None
  | Map tbl -> Term.Tbl.get tbl

let eval = find

let pp out = function
  | Empty -> Fmt.string out "(model)"
  | Map tbl ->
    let pp_pair out (t, v) =
      Fmt.fprintf out "(@[<1>%a@ := %a@])" Term.pp_debug t Term.pp_debug v
    in
    Fmt.fprintf out "(@[<hv>model@ %a@])" (Util.pp_iter pp_pair)
      (Term.Tbl.to_iter tbl)
