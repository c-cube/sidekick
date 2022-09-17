open Sidekick_core
module T = Term

type t = { m: Term.t T.Map.t } [@@unboxed]

let empty : t = { m = T.Map.empty }
let is_empty self = T.Map.is_empty self.m
let mem self t = T.Map.mem t self.m
let find self t = T.Map.find_opt t self.m
let eval = find
let add t v self : t = { m = T.Map.add t v self.m }
let keys self = T.Map.keys self.m
let to_iter self = T.Map.to_iter self.m

let pp out (self : t) =
  if is_empty self then
    Fmt.string out "(model)"
  else (
    let pp_pair out (t, v) =
      Fmt.fprintf out "(@[<1>%a@ := %a@])" Term.pp t Term.pp v
    in
    Fmt.fprintf out "(@[<hv>model@ %a@])" (Util.pp_iter pp_pair)
      (T.Map.to_iter self.m)
  )
