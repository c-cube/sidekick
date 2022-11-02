type t = int
type var = t

let pp = Fmt.int

type theory_view = ..

module Vec_of = Veci

(* TODO: GC API, + reuse existing slots that have been GC'd at the
   next [new_var_] allocation *)

type reason =
  | Decide of { level: int }
  | Propagate of { level: int; hyps: Vec_of.t; proof: Sidekick_proof.step_id }

let dummy_level_ = -1
let dummy_reason_ : reason = Decide { level = dummy_level_ }

type store = {
  tst: Term.store;
  of_term: t Term.Weak_map.t;
  term: Term.t Vec.t;
  level: Veci.t;
  value: Value.t option Vec.t;
  reason: reason Vec.t;
  theory_views: theory_view Vec.t;
  watches: t Vec.t Vec.t;
  has_value: Bitvec.t;
  new_vars: Vec_of.t;
}

(* create a new variable *)
let new_var_ (self : store) ~term:(term_for_v : Term.t) ~theory_view () : t =
  let v : t = Vec.size self.term in
  let {
    tst = _;
    of_term = _;
    term;
    level;
    value;
    watches;
    reason;
    theory_views;
    has_value;
    new_vars;
  } =
    self
  in
  Vec.push term term_for_v;
  Veci.push level dummy_level_;
  Vec.push value None;
  (* fake *)
  Vec.push reason dummy_reason_;
  Vec.push watches (Vec.create ());
  Vec.push theory_views theory_view;
  Bitvec.ensure_size has_value (v + 1);
  Bitvec.set has_value v false;
  Vec_of.push new_vars v;
  v

let[@inline] get_of_term (self : store) (t : Term.t) : t option =
  Term.Weak_map.find_opt self.of_term t

let[@inline] has_value (self : store) (v : t) : bool =
  Bitvec.get self.has_value v

let[@inline] level (self : store) (v : t) : int = Veci.get self.level v
let[@inline] value (self : store) (v : t) : _ option = Vec.get self.value v
let[@inline] theory_view (self : store) (v : t) = Vec.get self.theory_views v

let[@inline] bool_value (self : store) (v : t) : _ option =
  match Vec.get self.value v with
  | Some v when Term.is_true v -> Some true
  | Some v when Term.is_false v -> Some false
  | _ -> None

let[@inline] term (self : store) (v : t) : Term.t = Vec.get self.term v
let[@inline] reason (self : store) (v : t) : reason = Vec.get self.reason v
let[@inline] watchers (self : store) (v : t) : t Vec.t = Vec.get self.watches v

let[@inline] add_watcher (self : store) (v : t) ~watcher : unit =
  Vec.push (watchers self v) watcher

let assign (self : store) (v : t) ~value ~level ~reason : unit =
  Log.debugf 50 (fun k ->
      k "(@[cdsat.tvar.assign[lvl=%d]@ %a@ :val %a@])" level
        (Term.pp_limit ~max_depth:5 ~max_nodes:30)
        (term self v) Term.pp value);
  assert (level >= 0);
  Vec.set self.value v (Some value);
  Vec.set self.reason v reason;
  Veci.set self.level v level

let unassign (self : store) (v : t) : unit =
  Vec.set self.value v None;
  Veci.set self.level v dummy_level_;
  Vec.set self.reason v dummy_reason_

let pop_new_var self : _ option =
  if Vec_of.is_empty self.new_vars then
    None
  else
    Some (Vec_of.pop self.new_vars)

module Store = struct
  type t = store

  let tst self = self.tst

  let create tst : t =
    {
      tst;
      of_term = Term.Weak_map.create 256;
      reason = Vec.create ();
      term = Vec.create ();
      level = Veci.create ();
      watches = Vec.create ();
      value = Vec.create ();
      theory_views = Vec.create ();
      has_value = Bitvec.create ();
      new_vars = Vec_of.create ();
    }
end

let pp (self : store) out (v : t) : unit =
  let t = term self v in
  Fmt.fprintf out "(@[var[%d]@ :term %a@])" v
    (Term.pp_limit ~max_depth:5 ~max_nodes:30)
    t

module Internal = struct
  let create (self : store) (t : Term.t) ~theory_view : t =
    assert (not @@ Term.Weak_map.mem self.of_term t);
    let v = new_var_ self ~term:t ~theory_view () in
    Term.Weak_map.add self.of_term t v;
    v
end
