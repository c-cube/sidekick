
open Sidekick_base_term
module T = Sidekick_base_term.Term

let id_leq = ID.make "<="
let id_lt = ID.make "<"
let id_plus = ID.make "+"
let id_uminus = ID.make "-"
let id_mult = ID.make "*"

let fun_leq = Fun.mk_undef id_leq Ty.(Fun.mk [real; real] bool)
let fun_lt = Fun.mk_undef id_lt Ty.(Fun.mk [real; real] bool)
let fun_plus = Fun.mk_undef id_plus Ty.(Fun.mk [real; real] real)
let fun_uminus = Fun.mk_undef id_plus Ty.(Fun.mk [real] real)
let fun_times = Fun.mk_undef id_plus Ty.(Fun.mk [real; real] real)

let leq st a b = T.app_fun st fun_leq (IArray.of_array_unsafe [|a; b|])
let lt st a b = T.app_fun st fun_lt (IArray.of_array_unsafe [|a; b|])
let lt st a b = T.app_fun st fun_lt (IArray.of_array_unsafe [|a; b|])

let view_as_lra _ = assert false (* TODO *)

let mk_lra _ = assert false
