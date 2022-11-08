(** Plugin for uninterpreted symbols *)

open Sidekick_core

module type ARG = sig
  val is_unin_function : Term.t -> bool
end

(* store data for each unin function application *)
type TVar.theory_view +=
  | Unin_const of Term.t
  | Unin_fun of { f: Term.t; args: TVar.t array }

(* congruence table *)
module Cong_tbl = Backtrackable_tbl.Make (struct
  type t = { f: Term.t; args: Value.t array }

  let equal a b = Term.equal a.f b.f && CCArray.equal Value.equal a.args b.args
  let hash a = CCHash.(combine2 (Term.hash a.f) (array Value.hash a.args))
end)

(* an entry [f(values) -> value], used to detect congruence rule *)
type cong_entry = { v_args: TVar.t array; res: Value.t; v_res: TVar.t }

type t = {
  arg: (module ARG);
  vst: TVar.store;
  cong_table: cong_entry Cong_tbl.t;
}

let create arg vst : t = { arg; vst; cong_table = Cong_tbl.create ~size:256 () }
let push_level self = Cong_tbl.push_level self.cong_table
let pop_levels self n = Cong_tbl.pop_levels self.cong_table n

(* let other theories decide, depending on the type *)
let decide _ _ = None

(* FIXME: use on_event instead, watch (term + set of args) for congruence *)
let on_assign (self : t) _act (v : TVar.t) (value : Value.t) =
  match TVar.theory_view self.vst v with
  | Unin_const _ -> ()
  | Unin_fun { f = _; args } ->
    (* TODO: update congruence table *)
    Log.debugf 0 (fun k -> k "FIXME: congruence rule");
    ()
  | _ -> ()

(* handle new terms *)
let term_to_var_hooks (self : t) : _ list =
  let (module A) = self.arg in
  let h t2v (t : Term.t) : _ option =
    let f, args = Term.unfold_app t in
    if A.is_unin_function f then (
      (* convert arguments to vars *)
      let args = Util.array_of_list_map (Term_to_var.convert t2v) args in
      if Array.length args = 0 then
        Some (Unin_const t)
      else
        Some (Unin_fun { f; args })
    ) else
      None
  in
  [ h ]

let iter_theory_view _ (v : TVar.theory_view) k : unit =
  match v with
  | Unin_const _ -> ()
  | Unin_fun { f = _; args } -> Array.iter k args
  | _ -> ()

(* TODO: congruence rules *)

let builder ((module A : ARG) as arg) : Core.Plugin.builder =
  Core.Plugin.make_builder ~name:"uf" ~create:(create arg) ~push_level
    ~pop_levels ~iter_theory_view ~decide ~on_assign ~term_to_var_hooks ()
