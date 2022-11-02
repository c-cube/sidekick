type t = { var: TVar.t; sign: bool }

let[@inline] make sign var : t = { sign; var }
let[@inline] neg self = { self with sign = not self.sign }
let[@inline] abs self = { self with sign = true }
let[@inline] sign self = self.sign
let[@inline] var self = self.var

let pp vst out (self : t) =
  if self.sign then
    TVar.pp vst out self.var
  else
    Fmt.fprintf out "(@[not@ %a@])" (TVar.pp vst) self.var
