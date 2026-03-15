module T = Sidekick_cic_lib.Term
module C = Sidekick_cic_lib.Const

let binder_to_cic : Lean_term.binder -> T.binder = function
  | Lean_term.BD -> T.BD
  | Lean_term.BI -> T.BI
  | Lean_term.BS -> T.BS
  | Lean_term.BC -> T.BC

(* ctx: list of elaborated types for BVar 0, 1, ... (innermost first) *)
let rec elab ~(ctx : T.t list) (lt : Lean_term.t) : T.t =
  match lt with
  | Lean_term.Sort l -> T.type_of_univ l
  | Lean_term.BVar i -> T.bvar_i i
  | Lean_term.Const (n, ls) -> T.const (C.make n) ls
  | Lean_term.App (f, a) -> T.app (elab ~ctx f) (elab ~ctx a)
  | Lean_term.Lam (b, n, ty, body) ->
    let ty' = elab ~ctx ty in
    let body' = elab ~ctx:(ty' :: ctx) body in
    T.lam (binder_to_cic b) n ~var_ty:ty' body'
  | Lean_term.Pi (b, n, ty, body) ->
    let ty' = elab ~ctx ty in
    let body' = elab ~ctx:(ty' :: ctx) body in
    T.pi (binder_to_cic b) n ~var_ty:ty' body'

let elab_top lt = elab ~ctx:[] lt
