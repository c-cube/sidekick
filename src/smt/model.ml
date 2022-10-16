(** SMT models.

  The solver models are partially evaluated; the frontend might ask
  for values for terms not explicitly present in them.

*)

open Sigs

type t = { eval: Term.t -> value option; map: value Term.Map.t }

let is_empty self = Term.Map.is_empty self.map

let eval (self : t) (t : Term.t) : value option =
  try Some (Term.Map.find t self.map) with Not_found -> self.eval t

let pp out (self : t) =
  if is_empty self then
    Fmt.string out "(model)"
  else (
    let pp_pair out (t, v) =
      Fmt.fprintf out "(@[<1>%a@ := %a@])" Term.pp t Term.pp v
    in
    Fmt.fprintf out "(@[<hv>model@ %a@])" (Util.pp_iter pp_pair)
      (Term.Map.to_iter self.map)
  )
