open Types_
module T = Term

(* Pair-keyed table for def_eq cache *)
module T2_tbl = CCHashtbl.Make (struct
  type t = term * term

  let equal (a1, b1) (a2, b2) = T.equal a1 a2 && T.equal b1 b2
  let hash (a, b) = CCHash.combine3 91 (T.hash a) (T.hash b)
end)

(** Weak head normal form. Beta-reduces at the head until stuck. Memoised via
    [cache]. *)
let whnf ?(cache = T.Tbl.create 16) store e =
  let rec loop e =
    match T.Tbl.find_opt cache e with
    | Some v -> v
    | None ->
      let v = step e in
      T.Tbl.add cache e v;
      v
  and step e =
    match T.view e with
    | E_app (f, a) ->
      let f' = loop f in
      (match T.view f' with
      | E_lam (_, _, body) -> loop (T.DB.subst_db0 store body ~by:a)
      | _ ->
        if f == f' then
          e
        else
          T.app store f' a)
    | _ -> e
  in
  loop e

(** Definitional equality: WHNF both sides, then compare structurally. Uses
    [Level.judge_eq] for universe levels. Memoised via pair cache to handle
    sharing in DAGs. *)
let def_eq store e1 e2 =
  let whnf_cache = T.Tbl.create 16 in
  let eq_cache : bool T2_tbl.t = T2_tbl.create 16 in
  let whnf = whnf ~cache:whnf_cache store in

  let rec go e1 e2 =
    if T.equal e1 e2 then
      true
    else (
      (* canonical order to halve cache size *)
      let key =
        if T.compare e1 e2 <= 0 then
          e1, e2
        else
          e2, e1
      in
      match T2_tbl.find_opt eq_cache key with
      | Some b -> b
      | None ->
        (* assume true while recursing (for coinductive guard on open terms) *)
        T2_tbl.add eq_cache key true;
        let r = check e1 e2 in
        T2_tbl.replace eq_cache key r;
        r
    )
  and check e1 e2 =
    let e1 = whnf e1 in
    let e2 = whnf e2 in
    if T.equal e1 e2 then
      true
    else (
      match T.view e1, T.view e2 with
      | E_type l1, E_type l2 -> Level.judge_eq (T.Store.lvl_store store) l1 l2
      | E_var v1, E_var v2 -> Var.equal v1 v2
      | E_const c1, E_const c2 -> Const.equal c1 c2
      | E_bound_var b1, E_bound_var b2 -> Bvar.equal b1 b2
      | E_app (f1, a1), E_app (f2, a2) -> go f1 f2 && go a1 a2
      | E_lam (_, ty1, b1), E_lam (_, ty2, b2) -> go ty1 ty2 && go b1 b2
      | E_pi (_, ty1, b1), E_pi (_, ty2, b2) -> go ty1 ty2 && go b1 b2
      | _ -> false
    )
  in
  go e1 e2

(* Install into the kernel *)
let () = T.Internal_.def_eq_ref := def_eq
