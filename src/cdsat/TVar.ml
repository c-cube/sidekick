type t = int
type var = t

let pp = Fmt.int

module Vec_of = Veci

(* TODO: GC API, + reuse existing slots that have been GC'd at the
   next [new_var_] allocation *)

type reason =
  | Decide
  | Propagate of { level: int; hyps: Vec_of.t; proof: Sidekick_proof.step_id }

type store = {
  tst: Term.store;
  of_term: t Term.Weak_map.t;
  term: Term.t Vec.t;
  level: Veci.t;
  value: Value.t option Vec.t;
  reason: reason Vec.t;
  watches: t Vec.t Vec.t;
  has_value: Bitvec.t;
  new_vars: Vec_of.t;
}

(* create a new variable *)
let new_var_ (self : store) ~term:(term_for_v : Term.t) () : t =
  let v : t = Vec.size self.term in
  let {
    tst = _;
    of_term = _;
    term;
    level;
    value;
    watches;
    reason;
    has_value;
    new_vars;
  } =
    self
  in
  Vec.push term term_for_v;
  Veci.push level (-1);
  Vec.push value None;
  (* fake *)
  Vec.push reason Decide;
  Vec.push watches (Vec.create ());
  Bitvec.ensure_size has_value (v + 1);
  Bitvec.set has_value v false;
  Vec_of.push new_vars v;
  v

let of_term (self : store) (t : Term.t) : t =
  match Term.Weak_map.find_opt self.of_term t with
  | Some v -> v
  | None ->
    let v = new_var_ self ~term:t () in
    Term.Weak_map.add self.of_term t v;
    (* TODO: map sub-terms to variables. Perhaps preprocess-like hooks that
       will allow the variable to be properly defined in one theory? *)
    v

let[@inline] has_value (self : store) (v : t) : bool =
  Bitvec.get self.has_value v

let[@inline] level (self : store) (v : t) : int = Veci.get self.level v
let[@inline] value (self : store) (v : t) : _ option = Vec.get self.value v

let[@inline] set_value (self : store) (v : t) value : unit =
  Vec.set self.value v (Some value)

let[@inline] unset_value (self : store) (v : t) : unit =
  Vec.set self.value v None

let[@inline] term (self : store) (v : t) : Term.t = Vec.get self.term v
let[@inline] reason (self : store) (v : t) : reason = Vec.get self.reason v
let[@inline] watchers (self : store) (v : t) : t Vec.t = Vec.get self.watches v

let[@inline] add_watcher (self : store) (v : t) ~watcher : unit =
  Vec.push (watchers self v) watcher

let pop_new_var self : _ option =
  if Vec_of.is_empty self.new_vars then
    None
  else
    Some (Vec_of.pop self.new_vars)

module Store = struct
  type t = store

  let create tst : t =
    {
      tst;
      of_term = Term.Weak_map.create 256;
      reason = Vec.create ();
      term = Vec.create ();
      level = Veci.create ();
      watches = Vec.create ();
      value = Vec.create ();
      has_value = Bitvec.create ();
      new_vars = Vec_of.create ();
    }
end
