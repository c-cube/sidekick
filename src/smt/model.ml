(** SMT models.

  The solver models are partially evaluated; the frontend might ask
  for values for terms not explicitly present in them.

*)

open Sigs

type t = { eval: Term.t -> value option; map: value Term.Map.t }

let eval (self : t) (t : Term.t) : value option =
  try Some (Term.Map.find t self.map) with Not_found -> self.eval t
