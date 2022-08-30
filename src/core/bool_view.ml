(** Boolean-oriented view of terms *)

(** View *)
type 'a t =
  | B_bool of bool
  | B_not of 'a
  | B_and of 'a list
  | B_or of 'a list
  | B_imply of 'a * 'a
  | B_equiv of 'a * 'a
  | B_xor of 'a * 'a
  | B_eq of 'a * 'a
  | B_neq of 'a * 'a
  | B_ite of 'a * 'a * 'a
  | B_atom of 'a
