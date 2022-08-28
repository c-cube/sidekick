open Sidekick_core
module T = Term

type t = {
  tst: Term.store;
  processed: T.Set.t T.Tbl.t;  (** type -> set of terms *)
  unprocessed: T.t Vec.t;
  new_lits: Lit.t Vec.t;
  claims: Theory_id.Set.t T.Tbl.t;  (** term -> theories claiming it *)
  n_terms: int Stat.counter;
  n_lits: int Stat.counter;
}

let create ?(stat = Stat.global) tst : t =
  {
    tst;
    processed = T.Tbl.create 8;
    unprocessed = Vec.create ();
    claims = T.Tbl.create 8;
    new_lits = Vec.create ();
    n_terms = Stat.mk_int stat "smt.thcomb.terms";
    n_lits = Stat.mk_int stat "smt.thcomb.intf-lits";
  }

let processed_ (self : t) t : bool =
  let ty = T.ty t in
  match T.Tbl.find_opt self.processed ty with
  | None -> false
  | Some set -> T.Set.mem t set

let add_term_needing_combination (self : t) (t : T.t) : unit =
  if not (processed_ self t) then (
    Log.debugf 50 (fun k ->
        k "(@[th.comb.add-term-needing-comb@ `%a`@ :ty `%a`@])" T.pp t T.pp
          (T.ty t));
    Vec.push self.unprocessed t
  )

let claim_term (self : t) ~th_id (t : T.t) : unit =
  (* booleans don't need theory combination *)
  if T.is_bool (T.ty t) then
    ()
  else (
    Log.debugf 50 (fun k ->
        k "(@[th.comb.claim :th-id %a@ `%a`@])" Theory_id.pp th_id T.pp t);
    let set =
      try T.Tbl.find self.claims t with Not_found -> Theory_id.Set.empty
    in
    let set' = Theory_id.Set.add th_id set in
    if Theory_id.Set.(not (equal set set')) then (
      T.Tbl.replace self.claims t set';
      (* first time we have 2 theories, means we need combination *)
      if Theory_id.Set.cardinal set' = 2 then
        add_term_needing_combination self t
    )
  )

let pop_new_lits (self : t) : Lit.t list =
  (* first, process new terms, if any *)
  while not (Vec.is_empty self.unprocessed) do
    let t = Vec.pop_exn self.unprocessed in
    let ty = T.ty t in
    let set_for_ty =
      try T.Tbl.find self.processed ty with Not_found -> T.Set.empty
    in
    if not (T.Set.mem t set_for_ty) then (
      Stat.incr self.n_terms;

      (* now create [t=u] for each [u] in [set_for_ty] *)
      T.Set.iter
        (fun u ->
          let lit = Lit.make_eq self.tst t u in
          Stat.incr self.n_lits;
          Vec.push self.new_lits lit)
        set_for_ty;

      (* add [t] to the set of processed terms *)
      let new_set_for_ty = T.Set.add t set_for_ty in
      T.Tbl.replace self.processed ty new_set_for_ty
    )
  done;

  let lits = Vec.to_list self.new_lits in
  Vec.clear self.new_lits;
  lits
