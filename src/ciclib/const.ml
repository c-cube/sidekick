open Types_

type t = const = { c_name: string } [@@unboxed]

let[@inline] name self = self.c_name
let pp out (a : t) = Fmt.string out a.c_name
let make c_name : t = { c_name }
