
(** {1 Value} *)

open Base_types

type t = value

let true_ = V_bool true
let false_ = V_bool false
let[@inline] bool v = if v then true_ else false_

let mk_elt id ty : t = V_element {id; ty}

let[@inline] is_bool = function V_bool _ -> true | _ -> false
let[@inline] is_true = function V_bool true -> true | _ -> false
let[@inline] is_false = function V_bool false -> true | _ -> false

let equal = eq_value
let hash = hash_value
let pp = pp_value

let fresh (t:term) : t =
  mk_elt (ID.makef "v_%d" t.term_id) t.term_ty
