open Sidekick_core
open Sigs
include Base_types_
module Lit_tbl = Hashtbl.Make (Lit)

type cstore = {
  c_lits: atom array Vec.t; (* storage for clause content *)
  c_activity: Vec_float.t;
  c_recycle_idx: Veci.t; (* recycle clause numbers that were GC'd *)
  c_proof: Step_vec.t; (* clause -> proof_rule for its proof *)
  c_attached: Bitvec.t;
  c_marked: Bitvec.t;
  c_removable: Bitvec.t;
  c_dead: Bitvec.t;
}

type t = {
  (* variables *)
  v_of_lit: var Lit_tbl.t; (* lit -> var *)
  v_level: int Vec.t; (* decision/assignment level, or -1 *)
  v_heap_idx: int Vec.t; (* index in priority heap *)
  v_weight: Vec_float.t; (* heuristic activity *)
  v_reason: var_reason option Vec.t; (* reason for assignment *)
  v_seen: Bitvec.t; (* generic temporary marker *)
  v_default_polarity: Bitvec.t; (* default polarity in decisions *)
  v_last_polarity: Bitvec.t; (* last polarity when deciding this *)
  mutable v_count: int;
  (* atoms *)
  a_is_true: Bitvec.t;
  a_seen: Bitvec.t;
  a_form: Lit.t Vec.t;
  (* TODO: store watches in clauses instead *)
  a_watched: Clause0.CVec.t Vec.t;
  a_proof_lvl0: Proof.Step.id ATbl.t;
  (* atom -> proof for it to be true at level 0 *)
  stat_n_atoms: int Stat.counter;
  (* clauses *)
  c_store: cstore;
}

type store = t

let create ?(size = `Big) ~stat () : t =
  let size_map =
    match size with
    | `Tiny -> 8
    | `Small -> 16
    | `Big -> 4096
  in
  let stat_n_atoms = Stat.mk_int stat "sat.n-atoms" in
  {
    v_of_lit = Lit_tbl.create size_map;
    v_level = Vec.create ();
    v_heap_idx = Vec.create ();
    v_weight = Vec_float.create ();
    v_reason = Vec.create ();
    v_seen = Bitvec.create ();
    v_default_polarity = Bitvec.create ();
    v_last_polarity = Bitvec.create ();
    v_count = 0;
    a_is_true = Bitvec.create ();
    a_form = Vec.create ();
    a_watched = Vec.create ();
    a_seen = Bitvec.create ();
    a_proof_lvl0 = ATbl.create 16;
    stat_n_atoms;
    c_store =
      {
        c_lits = Vec.create ();
        c_activity = Vec_float.create ();
        c_recycle_idx = Veci.create ~cap:0 ();
        c_proof = Step_vec.create ~cap:0 ();
        c_dead = Bitvec.create ();
        c_attached = Bitvec.create ();
        c_removable = Bitvec.create ();
        c_marked = Bitvec.create ();
      };
  }

(** iterate on variables *)
let iter_vars self f =
  Vec.iteri self.v_level ~f:(fun i _ -> f (Var0.of_int_unsafe i))

module Var = struct
  include Var0

  let[@inline] level self v = Vec.get self.v_level (v : var :> int)
  let[@inline] set_level self v l = Vec.set self.v_level (v : var :> int) l
  let[@inline] reason self v = Vec.get self.v_reason (v : var :> int)
  let[@inline] set_reason self v r = Vec.set self.v_reason (v : var :> int) r
  let[@inline] weight self v = Vec_float.get self.v_weight (v : var :> int)

  let[@inline] set_weight self v w =
    Vec_float.set self.v_weight (v : var :> int) w

  let[@inline] mark self v = Bitvec.set self.v_seen (v : var :> int) true
  let[@inline] unmark self v = Bitvec.set self.v_seen (v : var :> int) false
  let[@inline] marked self v = Bitvec.get self.v_seen (v : var :> int)

  let[@inline] set_last_pol self v b =
    Bitvec.set self.v_last_polarity (v : var :> int) b

  let[@inline] last_pol self v =
    Bitvec.get self.v_last_polarity (v : var :> int)

  let[@inline] set_default_pol self v b =
    Bitvec.set self.v_default_polarity (v : var :> int) b;
    (* also update last polarity *)
    set_last_pol self v b

  let[@inline] default_pol self v =
    Bitvec.get self.v_default_polarity (v : var :> int)

  let[@inline] heap_idx self v = Vec.get self.v_heap_idx (v : var :> int)

  let[@inline] set_heap_idx self v i =
    Vec.set self.v_heap_idx (v : var :> int) i
end

module Atom = struct
  include Atom0

  let[@inline] lit self a = Vec.get self.a_form (a : atom :> int)
  let lit = lit
  let[@inline] mark self a = Bitvec.set self.a_seen (a : atom :> int) true
  let[@inline] unmark self a = Bitvec.set self.a_seen (a : atom :> int) false
  let[@inline] marked self a = Bitvec.get self.a_seen (a : atom :> int)
  let[@inline] watched self a = Vec.get self.a_watched (a : atom :> int)
  let[@inline] is_true self a = Bitvec.get self.a_is_true (a : atom :> int)

  let[@inline] set_is_true self a b =
    Bitvec.set self.a_is_true (a : atom :> int) b

  let[@inline] is_false self a = is_true self (neg a)
  let[@inline] has_value self a = is_true self a || is_false self a
  let[@inline] reason self a = Var.reason self (var a)
  let[@inline] level self a = Var.level self (var a)
  let[@inline] marked_both self a = marked self a && marked self (neg a)
  let proof_lvl0 self a = ATbl.get self.a_proof_lvl0 a
  let set_proof_lvl0 self a p = ATbl.replace self.a_proof_lvl0 a p
  let pp self fmt a = Lit.pp fmt (lit self a)

  let pp_a self fmt v =
    if Array.length v = 0 then
      Format.fprintf fmt "@<1>∅"
    else (
      pp self fmt v.(0);
      if Array.length v > 1 then
        for i = 1 to Array.length v - 1 do
          Format.fprintf fmt " @<1>∨ %a" (pp self) v.(i)
        done
    )

  (* Complete debug printing *)

  let[@inline] pp_sign a =
    if sign a then
      "+"
    else
      "-"

  (* print level+reason of assignment *)
  let debug_reason _self out = function
    | n, _ when n < 0 -> Format.fprintf out "%%"
    | n, None -> Format.fprintf out "%d" n
    | n, Some Decision -> Format.fprintf out "@@%d" n
    | n, Some (Bcp c) -> Format.fprintf out "->%d/%d" n (c :> int)
    | n, Some (Bcp_lazy _) -> Format.fprintf out "->%d/<lazy>" n

  let pp_level self out a =
    let v = var a in
    debug_reason self out (Var.level self v, Var.reason self v)

  let debug_value self out (a : atom) =
    if is_true self a then
      Format.fprintf out "T%a" (pp_level self) a
    else if is_false self a then
      Format.fprintf out "F%a" (pp_level self) a
    else
      ()

  let debug self out a =
    Format.fprintf out "%s%d[%a][atom:@[<hov>%a@]]" (pp_sign a)
      (var a : var :> int)
      (debug_value self) a Lit.pp (lit self a)

  let debug_a self out vec =
    Array.iter (fun a -> Format.fprintf out "@[%a@]@ " (debug self) a) vec
end

module Clause = struct
  include Clause0

  (* TODO: store watch lists inside clauses *)

  let make_a (store : store) ~removable (atoms : atom array) proof_step : t =
    let {
      c_recycle_idx;
      c_lits;
      c_activity;
      c_attached;
      c_dead;
      c_removable;
      c_marked;
      c_proof;
    } =
      store.c_store
    in
    (* allocate new ID *)
    let cid =
      if Veci.is_empty c_recycle_idx then
        Vec.size c_lits
      else
        Veci.pop c_recycle_idx
    in

    (* allocate space *)
    (let new_len = cid + 1 in
     Vec.ensure_size c_lits ~elt:[||] new_len;
     Vec_float.ensure_size c_activity new_len;
     Step_vec.ensure_size c_proof new_len;
     Bitvec.ensure_size c_attached new_len;
     Bitvec.ensure_size c_dead new_len;
     Bitvec.ensure_size c_removable new_len;
     Bitvec.ensure_size c_marked new_len;

     Bitvec.set c_removable cid removable);

    Vec.set c_lits cid atoms;
    Step_vec.set c_proof cid proof_step;

    let c = of_int_unsafe cid in
    c

  let make_l store ~removable atoms proof_rule : t =
    make_a store ~removable (Array.of_list atoms) proof_rule

  let[@inline] n_atoms (store : store) (c : t) : int =
    Array.length (Vec.get store.c_store.c_lits (c : t :> int))

  let[@inline] iter (store : store) ~f c =
    let { c_lits; _ } = store.c_store in
    Array.iter f (Vec.get c_lits (c : t :> int))

  exception Early_exit

  let for_all store ~f c =
    try
      iter store c ~f:(fun x -> if not (f x) then raise_notrace Early_exit);
      true
    with Early_exit -> false

  let fold (store : store) ~f acc c =
    let { c_lits; _ } = store.c_store in
    Array.fold_left f acc (Vec.get c_lits (c : t :> int))

  let[@inline] marked store c = Bitvec.get store.c_store.c_marked (c : t :> int)

  let[@inline] set_marked store c b =
    Bitvec.set store.c_store.c_marked (c : t :> int) b

  let[@inline] attached store c =
    Bitvec.get store.c_store.c_attached (c : t :> int)

  let[@inline] set_attached store c b =
    Bitvec.set store.c_store.c_attached (c : t :> int) b

  let[@inline] dead store c = Bitvec.get store.c_store.c_dead (c : t :> int)

  let[@inline] set_dead store c b =
    Bitvec.set store.c_store.c_dead (c : t :> int) b

  let[@inline] removable store c =
    Bitvec.get store.c_store.c_removable (c : t :> int)

  let[@inline] proof_step store c =
    Step_vec.get store.c_store.c_proof (c : t :> int)

  let dealloc store c : unit =
    assert (dead store c);
    let {
      c_lits;
      c_recycle_idx;
      c_activity;
      c_proof = _;
      c_dead;
      c_removable;
      c_attached;
      c_marked;
    } =
      store.c_store
    in

    (* clear data *)
    let cid = (c : t :> int) in
    Bitvec.set c_attached cid false;
    Bitvec.set c_dead cid false;
    Bitvec.set c_removable cid false;
    Bitvec.set c_marked cid false;
    Vec.set c_lits cid [||];
    Vec_float.set c_activity cid 0.;

    Veci.push c_recycle_idx cid;
    (* recycle idx *)
    ()

  let[@inline] activity store c =
    Vec_float.get store.c_store.c_activity (c : t :> int)

  let[@inline] set_activity store c f =
    Vec_float.set store.c_store.c_activity (c : t :> int) f

  let[@inline] atoms_a store c : atom array =
    Vec.get store.c_store.c_lits (c : t :> int)

  let lits_l store c : Lit.t list =
    let arr = atoms_a store c in
    Util.array_to_list_map (Atom.lit store) arr

  let lits_a store c : Lit.t array =
    let arr = atoms_a store c in
    Array.map (Atom.lit store) arr

  let lits_iter store c : Lit.t Iter.t =
    let arr = atoms_a store c in
    Iter.of_array arr |> Iter.map (Atom.lit store)

  let short_name _store c = Printf.sprintf "cl[%d]" (c : t :> int)

  let pp store fmt c =
    Format.fprintf fmt "(cl[%d] : %a"
      (c : t :> int)
      (Atom.pp_a store) (atoms_a store c)

  let debug store out c =
    let atoms = atoms_a store c in
    Format.fprintf out "(@[cl[%d]@ {@[<hov>%a@]}@])"
      (c : t :> int)
      (Atom.debug_a store) atoms
end

(* allocate new variable *)
let alloc_var_uncached_ ?default_pol:(pol = true) self (form : Lit.t) : var =
  let {
    v_count;
    v_of_lit;
    v_level;
    v_heap_idx;
    v_weight;
    v_reason;
    v_seen;
    v_default_polarity;
    v_last_polarity;
    stat_n_atoms;
    a_is_true;
    a_seen;
    a_watched;
    a_form;
    c_store = _;
    a_proof_lvl0 = _;
  } =
    self
  in

  let v_idx = v_count in
  let v = Var.of_int_unsafe v_idx in

  Stat.incr stat_n_atoms;

  self.v_count <- 1 + v_idx;
  Lit_tbl.add v_of_lit form v;
  Vec.push v_level (-1);
  Vec.push v_heap_idx (-1);
  Vec.push v_reason None;
  Vec_float.push v_weight 0.;
  Bitvec.ensure_size v_seen v_idx;
  Bitvec.ensure_size v_default_polarity v_idx;
  Bitvec.set v_default_polarity v_idx pol;
  Bitvec.ensure_size v_last_polarity v_idx;
  Bitvec.set v_last_polarity v_idx pol;

  assert (Vec.size a_form = 2 * (v : var :> int));
  Bitvec.ensure_size a_is_true (2 * (v : var :> int));
  Bitvec.ensure_size a_seen (2 * (v : var :> int));
  Vec.push a_form form;
  Vec.push a_watched (CVec.create ~cap:0 ());
  Vec.push a_form (Lit.neg form);
  Vec.push a_watched (CVec.create ~cap:0 ());
  assert (Vec.get a_form (Atom.of_var v : atom :> int) == form);

  v

(* create new variable *)
let alloc_var (self : t) ?default_pol (lit : Lit.t) : var * same_sign =
  let lit, same_sign = Lit.norm_sign lit in
  try Lit_tbl.find self.v_of_lit lit, same_sign
  with Not_found ->
    let v = alloc_var_uncached_ ?default_pol self lit in
    v, same_sign

let clear_var (self : t) (v : var) : unit =
  Var.unmark self v;
  Atom.unmark self (Atom.pa v);
  Atom.unmark self (Atom.na v);
  ()

let atom_of_var_ v same_sign : atom =
  if same_sign then
    Atom.pa v
  else
    Atom.na v

let alloc_atom (self : t) ?default_pol lit : atom =
  let var, same_sign = alloc_var self ?default_pol lit in
  atom_of_var_ var same_sign

let find_atom (self : t) lit : atom option =
  let lit, same_sign = Lit.norm_sign lit in
  match Lit_tbl.find self.v_of_lit lit with
  | v -> Some (atom_of_var_ v same_sign)
  | exception Not_found -> None
