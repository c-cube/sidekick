
(** {1 Theory of Booleans} *)

type term = Sidekick_smt.Term.t

module Intf = Bool_intf
module Bool_term = Bool_term
module Th_dyn_tseitin = Th_dyn_tseitin

type 'a view = 'a Intf.view =
  | B_not of 'a
  | B_eq of 'a * 'a
  | B_and of 'a IArray.t
  | B_or of 'a IArray.t
  | B_imply of 'a IArray.t * 'a
  | B_distinct of 'a IArray.t
  | B_atom of 'a

module type BOOL_TERM = Intf.BOOL_TERM

(** Dynamic Tseitin transformation *)
let th_dynamic_tseitin =
  let module Th = Th_dyn_tseitin.Make(Bool_term) in
  Th.th
