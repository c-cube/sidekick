(** Encode sidekick [Term.t] values into minidag nodes.

    Uses the term command vocabulary from [ext-term.json]:
      t.type  t.v  t.bv  t.c  t.@  t.\  t.->
      cst

    Constants are encoded with the [cst] command (name + type).
    Terms are memoized: [Term.Tbl] for terms, [Const_tbl] for constants.
*)

open Sidekick_core
module E = Sidekick_minidag.Encode
module Const_tbl = CCHashtbl.Make (Const)

type t = {
  enc: E.t;
  term_cache: E.offset Term.Tbl.t;
  const_cache: E.offset Const_tbl.t;
}

let create enc : t =
  { enc; term_cache = Term.Tbl.create 256; const_cache = Const_tbl.create 64 }

let rec encode_const (self : t) (c : Const.t) : E.offset =
  match Const_tbl.find_opt self.const_cache c with
  | Some off -> off
  | None ->
    let ty_off = encode_term self c.Const.c_ty in
    let name = Format.asprintf "%a" Const.pp c in
    let off =
      E.write_node self.enc "cst" (fun nd ->
          E.string nd name;
          E.ref nd ty_off)
    in
    Const_tbl.replace self.const_cache c off;
    off

and encode_term (self : t) (t : Term.t) : E.offset =
  match Term.Tbl.find_opt self.term_cache t with
  | Some off -> off
  | None ->
    let off = encode_term_uncached self t in
    Term.Tbl.replace self.term_cache t off;
    off

and encode_term_uncached (self : t) (t : Term.t) : E.offset =
  let nd cmd f = E.write_node self.enc cmd f in
  match Term.view t with
  | Term.E_type _ -> nd "t.type" (fun _ -> ())

  | Term.E_const c ->
    let c_off = encode_const self c in
    nd "t.c" (fun e -> E.ref e c_off)

  | Term.E_app (f, a) ->
    let f_off = encode_term self f and a_off = encode_term self a in
    nd "t.@" (fun e -> E.ref e f_off; E.ref e a_off)

  | Term.E_lam (name, ty, body) ->
    let ty_off = encode_term self ty and body_off = encode_term self body in
    nd "t.\\" (fun e -> E.string e name; E.ref e ty_off; E.ref e body_off)

  | Term.E_pi (_name, dom, body) ->
    let dom_off = encode_term self dom and body_off = encode_term self body in
    nd "t.->" (fun e -> E.ref e dom_off; E.ref e body_off)

  | Term.E_var v ->
    let ty_off = encode_term self (Var.ty v) in
    nd "t.v" (fun e -> E.string e (Var.name v); E.ref e ty_off)

  | Term.E_bound_var bv ->
    let ty_off = encode_term self bv.bv_ty in
    nd "t.bv" (fun e -> E.int e bv.bv_idx; E.ref e ty_off)

  | Term.E_app_fold { f; args; acc0 } ->
    (* Left-spine of applications: (((f acc0) arg0) arg1) ... *)
    let mk_app l r = nd "t.@" (fun e -> E.ref e l; E.ref e r) in
    let base = mk_app (encode_term self f) (encode_term self acc0) in
    List.fold_left (fun acc arg -> mk_app acc (encode_term self arg)) base args

(** Encode a literal: positive → its term; negative → [not t]. *)
let encode_lit (self : t) (tst : Term.store) (lit : Lit.t) : E.offset =
  let t = if Lit.sign lit then Lit.term lit else Term.not tst (Lit.term lit) in
  encode_term self t
