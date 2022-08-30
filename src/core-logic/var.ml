open Types_

type t = var = { v_name: string; v_ty: term }

include Var_

let[@inline] name v = v.v_name
let[@inline] ty self = self.v_ty
let[@inline] pp out v1 = Fmt.string out v1.v_name
let make v_name v_ty : t = { v_name; v_ty }
let makef fmt ty = Fmt.kasprintf (fun s -> make s ty) fmt

let pp_with_ty out v =
  Fmt.fprintf out "(@[%s :@ %a@])" v.v_name !Term_.pp_debug_ v.v_ty
