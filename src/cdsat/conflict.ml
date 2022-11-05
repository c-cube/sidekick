type t = { vst: TVar.store; lit: TLit.t; propagate_reason: Reason.t }

let pp out (self : t) =
  Fmt.fprintf out "(@[conflict %a@])" (TLit.pp self.vst) self.lit

let make vst ~lit ~propagate_reason () : t = { vst; lit; propagate_reason }
