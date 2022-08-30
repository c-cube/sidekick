open Types_
module M = Var_.Map

type t = subst

let empty = { m = M.empty }
let is_empty self = M.is_empty self.m
let add v t self = { m = M.add v t self.m }

let pp out (self : t) =
  if is_empty self then
    Fmt.string out "(subst)"
  else (
    let pp_pair out (v, t) =
      Fmt.fprintf out "(@[%a := %a@])" Var.pp v !Term_.pp_debug_ t
    in
    Fmt.fprintf out "(@[subst@ %a@])" (Util.pp_iter pp_pair) (M.to_iter self.m)
  )

let of_list l = { m = M.of_list l }
let of_iter it = { m = M.of_iter it }
let to_iter self = M.to_iter self.m

let apply (store : Term.store) ~recursive (self : t) (e : term) : term =
  Term.Internal_.subst_ store ~recursive e self
