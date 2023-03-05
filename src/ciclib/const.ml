open Types_

type t = const = { c_name: string; c_ty: term }

let[@inline] name self = self.c_name
let[@inline] ty self = self.c_ty
let pp out (a : t) = Fmt.string out a.c_name
let make c_name ~ty:c_ty : t = { c_name; c_ty }
