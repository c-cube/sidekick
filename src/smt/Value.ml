
(** {1 Value} *)

open Solver_types

type t = value

let true_ = V_bool true
let false_ = V_bool false
let bool v = V_bool v

let mk_elt id ty : t = V_element {id; ty}

let is_bool = function V_bool _ -> true | _ -> false
let is_true = function V_bool true -> true | _ -> false
let is_false = function V_bool false -> true | _ -> false

let equal = eq_value
let hash = hash_value
let pp = pp_value

let fresh (t:term) : t =
  mk_elt (ID.makef "v_%d" t.term_id) t.term_ty
