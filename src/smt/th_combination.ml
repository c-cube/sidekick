open Sidekick_core
module T = Term

type t = {
  tst: Term.store;
  claims: Theory_id.t T.Tbl.t;  (** type -> theory claiming it *)
  processed: T.Set.t T.Tbl.t;  (** type -> set of terms *)
  unprocessed: T.t Vec.t;
  n_terms: int Stat.counter;
  n_lits: int Stat.counter;
}

let create ?(stat = Stat.global) tst : t =
  {
    tst;
    claims = T.Tbl.create 8;
    processed = T.Tbl.create 8;
    unprocessed = Vec.create ();
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
    Log.debugf 50 (fun k -> k "(@[th.comb.add-term-needing-comb@ %a@])" T.pp t);
    Vec.push self.unprocessed t
  )

let pop_new_lits (self : t) : Lit.t list =
  let lits = ref [] in

  (* first, process new terms, if any *)
  while not (Vec.is_empty self.unprocessed) do
    let t = Vec.pop_exn self.unprocessed in
    let ty = T.ty t in
    let set_for_ty =
      try T.Tbl.find self.processed ty with Not_found -> T.Set.empty
    in
    if not (T.Set.mem t set_for_ty) then (
      Stat.incr self.n_terms;
      Log.debugf 0 (fun k -> k "NEED TH COMBINATION %a" T.pp t);

      (* now create [t=u] for each [u] in [set_for_ty], and add it to [lits] *)
      T.Set.iter
        (fun u ->
          let lit = Lit.make_eq self.tst t u in
          Stat.incr self.n_lits;
          lits := lit :: !lits)
        set_for_ty;

      (* add [t] to the set of processed terms *)
      let new_set_for_ty = T.Set.add t set_for_ty in
      T.Tbl.replace self.processed ty new_set_for_ty
    )
  done;

  !lits

let claim_sort (self : t) ~th_id ~ty : unit =
  match T.Tbl.find_opt self.claims ty with
  | Some id' ->
    if not (Theory_id.equal th_id id') then
      Error.errorf "Type %a is claimed by two distinct theories" Term.pp ty
  | None when T.is_bool ty -> Error.errorf "Cannot claim type Bool"
  | None ->
    Log.debugf 3 (fun k ->
        k "(@[th-comb.claim-ty@ :th-id %a@ :ty %a@])" Theory_id.pp th_id Term.pp
          ty);
    T.Tbl.add self.claims ty th_id

let[@inline] claimed_by (self : t) ~ty : _ option =
  T.Tbl.find_opt self.claims ty
