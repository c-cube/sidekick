
module type PLUGIN = sig
  val has_theory : bool
  (** [true] iff the solver is parametrized by a theory, not just
      pure SAT. *)

  include Solver_intf.PLUGIN_CDCL_T
end

module type S = Solver_intf.S
module type PLUGIN_CDCL_T = Solver_intf.PLUGIN_CDCL_T

let invalid_argf fmt =
  Format.kasprintf (fun msg -> invalid_arg ("sidekick.sat: " ^ msg)) fmt

module type INT_ID = sig
  type t = private int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val to_int : t -> int
  val of_int_unsafe : int -> t
end

module Mk_int_id() = struct
  type t = int
  let equal : t -> t -> bool = (=)
  let compare : t -> t -> int = compare
  let hash = CCHash.int
  let[@inline] to_int i = i
  external of_int_unsafe : int -> t = "%identity"
end

module Make(Plugin : PLUGIN)
= struct
  module Formula = Plugin.Formula

  type formula = Formula.t
  type theory = Plugin.t
  type lemma = Plugin.proof

  (* ### types ### *)

  (* a boolean variable (positive int) *)
  module Var0 : sig
    include INT_ID
    module Set : Set.S with type elt = t
  end = struct
    include Mk_int_id()
    module Set = Util.Int_set
  end
  type var = Var0.t

  (* a signed atom. +v is (v << 1), -v is (v<<1 | 1) *)
  module Atom0 : sig
    include INT_ID
    val neg : t -> t
    val sign : t -> bool

    val of_var : var -> t
    val var : t -> var
    val abs : t -> t
    val pa : var -> t
    val na : var -> t
    module Set : CCSet.S with type elt = t
  end = struct
    include Mk_int_id()
    let[@inline] neg i = (i lxor 1)
    let[@inline] sign i = (i land 1) = 0

    let[@inline] pa v = (v:var:>int) lsl 1
    let of_var = pa
    let[@inline] abs a = a land (lnot 1)
    let[@inline] var a = Var0.of_int_unsafe (a lsr 1)
    let[@inline] na v = (((v:var:>int) lsl 1) lor 1)
    module Set = Util.Int_set
  end
  type atom = Atom0.t

  module Clause0 : sig
    include INT_ID
    module Tbl : Hashtbl.S with type key = t
  end = struct
    include Mk_int_id()
    module Tbl = Util.Int_tbl
  end
  type clause = Clause0.t

  (* TODO: remove, replace with user-provided proof trackng device?
     for pure SAT, [reason] is sufficient *)
  type premise =
    | Hyp of lemma
    | Local
    | Lemma of lemma
    | History of clause list
    | Empty_premise

  and reason =
    | Decision
    | Bcp of clause
    | Bcp_lazy of clause lazy_t

  let kind_of_premise p = match p with
    | Hyp _ -> "H"
    | Lemma _ -> "T"
    | Local -> "L"
    | History _ -> "C"
    | Empty_premise -> ""

  (* ### stores ### *)

  module Form_tbl = Hashtbl.Make(Formula)

  (* variable/atom store *)
  module Store = struct
    type cstore = {
      c_lits: atom array Vec.t; (* storage for clause content *)
      c_activity: Vec_float.t;
      c_premise: premise Vec.t;
      c_recycle_idx: VecI32.t; (* recycle clause numbers that were GC'd *)
      c_attached: Bitvec.t;
      c_marked: Bitvec.t; (* TODO : remove *)
      c_removable: Bitvec.t;
      c_dead: Bitvec.t;
    }

    type t = {
      (* variables *)
      v_of_form: var Form_tbl.t;
      v_level: int Vec.t;
      v_heap_idx: int Vec.t;
      v_weight: Vec_float.t;
      v_reason: reason option Vec.t;
      v_seen: Bitvec.t;
      v_default_polarity: Bitvec.t;
      mutable v_count : int;

      (* atoms *)
      a_is_true: Bitvec.t;
      a_seen: Bitvec.t;
      a_form: formula Vec.t;
      (* TODO: store watches in clauses instead *)
      a_watched: clause Vec.t Vec.t;

      (* clauses *)
      c_store: cstore;
    }
    type store = t

    let create ?(size=`Big) () : t =
      let size_map = match size with
        | `Tiny -> 8
        | `Small -> 16
        | `Big -> 4096
      in
      { v_of_form = Form_tbl.create size_map;
        v_level = Vec.create();
        v_heap_idx = Vec.create();
        v_weight = Vec_float.create();
        v_reason = Vec.create();
        v_seen = Bitvec.create();
        v_default_polarity = Bitvec.create();
        v_count = 0;
        a_is_true=Bitvec.create();
        a_form=Vec.create();
        a_watched=Vec.create();
        a_seen=Bitvec.create();
        c_store={
          c_lits=Vec.create();
          c_activity=Vec_float.create();
          c_premise=Vec.create();
          c_recycle_idx=VecI32.create ~cap:0 ();
          c_dead=Bitvec.create();
          c_attached=Bitvec.create();
          c_removable=Bitvec.create();
          c_marked=Bitvec.create();
        }
      }

    (** Number of variables *)
    let[@inline] n_vars self : int = Vec.size self.v_level

    (** iterate on variables *)
    let iter_vars self f =
      Vec.iteri (fun i _ -> f (Var0.of_int_unsafe i)) self.v_level

    module Var = struct
      include Var0
      let[@inline] level self v = Vec.get self.v_level (v:var:>int)
      let[@inline] set_level self v l = Vec.set self.v_level (v:var:>int) l
      let[@inline] reason self v = Vec.get self.v_reason (v:var:>int)
      let[@inline] set_reason self v r = Vec.set self.v_reason (v:var:>int) r
      let[@inline] weight self v = Vec_float.get self.v_weight (v:var:>int)
      let[@inline] set_weight self v w = Vec_float.set self.v_weight (v:var:>int) w
      let[@inline] mark self v = Bitvec.set self.v_seen (v:var:>int) true
      let[@inline] unmark self v = Bitvec.set self.v_seen (v:var:>int) false
      let[@inline] marked self v = Bitvec.get self.v_seen (v:var:>int)
      let[@inline] set_default_pol self v b = Bitvec.set self.v_default_polarity (v:var:>int) b
      let[@inline] default_pol self v = Bitvec.get self.v_default_polarity (v:var:>int)
      let[@inline] heap_idx self v = Vec.get self.v_heap_idx (v:var:>int)
      let[@inline] set_heap_idx self v i = Vec.set self.v_heap_idx (v:var:>int) i
    end

    module Atom = struct
      include Atom0
      let[@inline] lit self a = Vec.get self.a_form (a:atom:>int)
      let formula = lit
      let[@inline] mark self a = Bitvec.set self.a_seen (a:atom:>int) true
      let[@inline] unmark self a = Bitvec.set self.a_seen (a:atom:>int) false
      let[@inline] marked self a = Bitvec.get self.a_seen (a:atom:>int)
      let[@inline] watched self a = Vec.get self.a_watched (a:atom:>int)
      let[@inline] is_true self a = Bitvec.get self.a_is_true (a:atom:>int)
      let[@inline] set_is_true self a b = Bitvec.set self.a_is_true (a:atom:>int) b

      let[@inline] is_false self a = is_true self (neg a)
      let[@inline] has_value self a = is_true self a || is_false self a

      let[@inline] reason self a = Var.reason self (var a)
      let[@inline] level self a = Var.level self (var a)
      let[@inline] marked_both self a = marked self a && marked self (neg a)

      let pp self fmt a = Formula.pp fmt (lit self a)

      let pp_a self fmt v =
        if Array.length v = 0 then (
          Format.fprintf fmt "@<1>∅"
        ) else (
          pp self fmt v.(0);
          if (Array.length v) > 1 then begin
            for i = 1 to (Array.length v) - 1 do
              Format.fprintf fmt " @<1>∨ %a" (pp self) v.(i)
            done
          end
        )

      (* Complete debug printing *)

      let[@inline] pp_sign a = if sign a then "+" else "-"

      (* print level+reason of assignment *)
      let debug_reason self out = function
        | n, _ when n < 0 -> Format.fprintf out "%%"
        | n, None -> Format.fprintf out "%d" n
        | n, Some Decision -> Format.fprintf out "@@%d" n
        | n, Some Bcp c ->
          let premise = Vec.get self.c_store.c_premise (c:>int) in
          Format.fprintf out "->%d/%s/%d" n (kind_of_premise premise) (c:>int)
        | n, Some (Bcp_lazy _) -> Format.fprintf out "->%d/<lazy>" n

      let pp_level self out a =
        let v = var a in
        debug_reason self out (Var.level self v, Var.reason self v)

      let debug_value self out (a:atom) =
        if is_true self a then Format.fprintf out "T%a" (pp_level self) a
        else if is_false self a then Format.fprintf out "F%a" (pp_level self) a
        else ()

      let debug self out a =
        Format.fprintf out "%s%d[%a][atom:@[<hov>%a@]]"
          (pp_sign a) (var a:var:>int) (debug_value self) a
          Formula.pp (lit self a)

      let debug_a self out vec =
        Array.iter (fun a -> Format.fprintf out "@[%a@]@ " (debug self) a) vec
      let debug_l self out l =
        List.iter (fun a -> Format.fprintf out "@[%a@]@ " (debug self) a) l
    end

    module Clause : sig
      include module type of Clause0 with type t = Clause0.t

      (** Make a clause with the given atoms *)

      val make_a : store -> removable:bool -> atom array -> premise -> t
      val make_l : store -> removable:bool -> atom list -> premise -> t
      val make_vec : store -> removable:bool -> atom Vec.t -> premise -> t

      val premise : store -> t -> premise

      val n_atoms : store -> t -> int

      val marked : store -> t -> bool
      val set_marked : store -> t -> bool -> unit
      val attached : store -> t -> bool
      val set_attached : store -> t -> bool -> unit
      val removable : store -> t -> bool
      val set_removable : store -> t -> bool -> unit

      val dead : store -> t -> bool
      val set_dead : store -> t -> bool -> unit
      val dealloc : store -> t -> unit
      (** Delete the clause *)

      val activity : store -> t -> float
      val set_activity : store -> t -> float -> unit

      val iter : store -> f:(atom -> unit) -> t -> unit
      val fold : store -> f:('a -> atom -> 'a) -> 'a -> t -> 'a
      val for_all : store -> f:(atom -> bool) -> t -> bool
      val exists : store -> f:(atom -> bool) -> t -> bool

      val atoms_a : store -> t -> atom array
      val atoms_l : store -> t -> atom list (* allocates *)
      val atoms_iter : store -> t -> atom Iter.t

      val short_name : store -> t -> string
      val pp : store -> Format.formatter -> t -> unit
      val debug : store -> Format.formatter -> t -> unit
    end = struct
      include Clause0

      (* TODO: store watch lists inside clauses *)

      let make_a (store:store) ~removable (atoms:atom array) premise : t =
        let {
          c_recycle_idx; c_lits; c_activity; c_premise;
          c_attached; c_dead; c_removable; c_marked;
        } = store.c_store in
        (* allocate new ID *)
        let cid =
          if VecI32.is_empty c_recycle_idx then (
            Vec.size c_lits
          ) else VecI32.pop c_recycle_idx
        in

        (* allocate space *)
        begin
          let new_len = cid + 1 in
          Vec.ensure_size c_lits [||] new_len;
          Vec.ensure_size c_premise Empty_premise new_len;
          Vec_float.ensure_size c_activity new_len;
          Bitvec.ensure_size c_attached new_len;
          Bitvec.ensure_size c_dead new_len;
          Bitvec.ensure_size c_removable new_len;
          Bitvec.ensure_size c_marked new_len;

          Bitvec.set c_removable cid removable;
        end;

        Vec.set c_lits cid atoms;
        Vec.set c_premise cid premise;

        let c = of_int_unsafe cid in
        c

      let make_l store ~removable atoms premise : t =
        make_a store ~removable (Array.of_list atoms) premise

      let make_vec store ~removable atoms premise : t =
        make_a store ~removable (Vec.to_array atoms) premise

      let[@inline] n_atoms (store:store) (c:t) : int =
        Array.length (Vec.get store.c_store.c_lits (c:t:>int))

      let[@inline] iter (store:store) ~f c =
        let {c_lits; _} = store.c_store in
        Array.iter f (Vec.get c_lits (c:t:>int))

      exception Early_exit

      let for_all store ~f c =
        try
          iter store c ~f:(fun x -> if not (f x) then raise_notrace Early_exit);
          true
        with Early_exit -> false

      let exists store ~f c =
        try
          iter store c ~f:(fun x -> if f x then raise_notrace Early_exit);
          false
        with Early_exit -> true

      let fold (store:store) ~f acc c =
        let {c_lits; _} = store.c_store in
        Array.fold_left f acc (Vec.get c_lits (c:t:>int))

      let[@inline] premise store c = Vec.get store.c_store.c_premise (c:t:>int)
      let[@inline] marked store c = Bitvec.get store.c_store.c_marked (c:t:>int)
      let[@inline] set_marked store c b = Bitvec.set store.c_store.c_marked (c:t:>int) b
      let[@inline] attached store c = Bitvec.get store.c_store.c_attached (c:t:>int)
      let[@inline] set_attached store c b = Bitvec.set store.c_store.c_attached (c:t:>int) b
      let[@inline] dead store c = Bitvec.get store.c_store.c_dead (c:t:>int)
      let[@inline] set_dead store c b = Bitvec.set store.c_store.c_dead (c:t:>int) b
      let[@inline] removable store c = Bitvec.get store.c_store.c_removable (c:t:>int)
      let[@inline] set_removable store c b = Bitvec.set store.c_store.c_removable (c:t:>int) b

      (* FIXME: actually GC the clause, recycle index, and remove it
         somehow from the watch lists *)
      let dealloc store c : unit =
        set_dead store c true;
        assert (dead store c);
        ()

      let copy_flags store c1 c2 : unit =
        set_removable store c2 (removable store c1);
        ()

      let[@inline] activity store c = Vec_float.get store.c_store.c_activity (c:t:>int)
      let[@inline] set_activity store c f = Vec_float.set store.c_store.c_activity (c:t:>int) f

      let[@inline] make_removable store l premise =
        make_l store ~removable:true l premise

      let[@inline] make_removable_a store a premise =
        make_a store ~removable:true a premise

      let[@inline] make_permanent store l premise =
        let c = make_l store ~removable:false l premise in
        assert (not (removable store c)); (* permanent by default *)
        c

      let[@inline] atoms_a store c : atom array =
        Vec.get store.c_store.c_lits (c:t:>int)
      let atoms_l store c : _ list = Array.to_list (atoms_a store c)
      let atoms_iter store c = fun k -> iter store c ~f:k

      let short_name store c =
        let p = premise store c in
        Printf.sprintf "%s%d" (kind_of_premise p) (c:t:>int)

      let pp store fmt c =
        let p = premise store c in
        Format.fprintf fmt "(cl[%s%d] : %a" (kind_of_premise p) (c:t:>int)
          (Atom.pp_a store) (atoms_a store c)

      let debug_premise out = function
        | Hyp _ -> Format.fprintf out "hyp"
        | Lemma _ -> Format.fprintf out "th_lemma"
        | Local -> Format.fprintf out "local"
        | History v as p ->
          Format.fprintf out "(@[res";
          List.iter (fun c -> Format.fprintf out "@ %s%d," (kind_of_premise p) (c:t:>int)) v;
          Format.fprintf out "@])"
        | Empty_premise -> Format.fprintf out "none"

      let debug store out c =
        let atoms = atoms_a store c in
        let p = premise store c in
        Format.fprintf out
          "(@[cl[%s%d]@ {@[<hov>%a@]}@ :premise %a@])"
          (kind_of_premise p) (c:t:>int)
          (Atom.debug_a store) atoms debug_premise p
    end

    (* allocate new variable *)
    let alloc_var_uncached_ ?default_pol:(pol=true) self (form:formula) : var =
      let {v_count; v_of_form; v_level; v_heap_idx; v_weight;
           v_reason; v_seen; v_default_polarity;
           a_is_true; a_seen; a_watched; a_form; c_store=_;
          } = self in

      let v_idx = v_count in
      let v = Var.of_int_unsafe v_idx in

      self.v_count <- 1 + v_idx;
      Form_tbl.add v_of_form form v;
      Vec.push v_level (-1);
      Vec.push v_heap_idx (-1);
      Vec.push v_reason None;
      Vec_float.push v_weight 0.;
      Bitvec.ensure_size v_seen v_idx;
      Bitvec.ensure_size v_default_polarity v_idx;
      Bitvec.set v_default_polarity v_idx pol;

      assert (Vec.size a_form = 2 * (v:var:>int));
      Bitvec.ensure_size a_is_true (2*(v:var:>int));
      Bitvec.ensure_size a_seen (2*(v:var:>int));
      Vec.push a_form form;
      Vec.push a_watched (Vec.create());
      Vec.push a_form (Formula.neg form);
      Vec.push a_watched (Vec.create());
      assert (Vec.get a_form (Atom.of_var v:atom:>int) == form);

      v

    (* create new variable *)
    let alloc_var (self:t) ?default_pol (t:formula) : var * Solver_intf.negated =
      let form, negated = Formula.norm t in
      try Form_tbl.find self.v_of_form form, negated
      with Not_found ->
        let v = alloc_var_uncached_ ?default_pol self form in
        v, negated

    let clear_var (self:t) (v:var) : unit =
      Var.unmark self v;
      Atom.unmark self (Atom.pa v);
      Atom.unmark self (Atom.na v);
      ()

    let alloc_atom (self:t) ?default_pol lit : atom =
      let var, negated = alloc_var self ?default_pol lit in
      match negated with
      | Solver_intf.Same_sign -> Atom.pa var
      | Solver_intf.Negated -> Atom.na var
  end
  type store = Store.t

  module Atom = Store.Atom
  module Var = Store.Var
  module Clause = Store.Clause

  (* TODO: mostly, move into a functor outside that works on integers *)
  module Proof =  struct
    exception Resolution_error of string

    type atom = Atom.t
    type clause = Clause.t
    type formula = Formula.t
    type lemma = Plugin.proof
    type nonrec store = store

    let error_res_f msg = Format.kasprintf (fun s -> raise (Resolution_error s)) msg

    let[@inline] clear_var_of_ store (a:atom) = Store.clear_var store (Atom.var a)

    (* Compute resolution of 2 clauses.
       returns [pivots, resulting_atoms] *)
    let resolve store (c1:clause) (c2:clause) : atom list * atom list =
      (* invariants: only atoms in [c2] are marked, and the pivot is
         cleared when traversing [c1] *)
      Clause.iter store c2 ~f:(Atom.mark store);
      let pivots = ref [] in
      let l =
        Clause.fold store [] c1
          ~f:(fun l a ->
             if Atom.marked store a then l
             else if Atom.marked store (Atom.neg a) then (
               pivots := (Atom.abs a) :: !pivots;
               clear_var_of_ store a;
               l
             ) else a::l)
      in
      let l =
        Clause.fold store l c2
          ~f:(fun l a -> if Atom.marked store a then a::l else l)
      in
      Clause.iter store c2 ~f:(clear_var_of_ store);
      !pivots, l

    (* [find_dups c] returns a list of duplicate atoms, and the deduplicated list *)
    let find_dups (store:store) (c:clause) : atom list * atom list =
      let res =
        Clause.fold store ([], []) c
          ~f:(fun (dups,l) a ->
             if Atom.marked store a then (
               a::dups, l
             ) else (
               Atom.mark store a;
               dups, a::l
             ))
      in
      Clause.iter store c ~f:(clear_var_of_ store);
      res

    (* do [c1] and [c2] have the same lits, modulo reordering and duplicates? *)
    let same_lits store (c1:atom Iter.t) (c2:atom Iter.t): bool =
      let subset a b =
        Iter.iter (Atom.mark store) b;
        let res = Iter.for_all (Atom.marked store) a in
        Iter.iter (clear_var_of_ store) b;
        res
      in
      subset c1 c2 && subset c2 c1

    let prove (store:store) conclusion =
      match Clause.premise store conclusion with
      | History [] -> assert false
      | Empty_premise -> raise Solver_intf.No_proof
      | _ -> conclusion

    let rec set_atom_proof store a =
      let aux acc b =
        if Atom.equal (Atom.neg a) b then acc
        else set_atom_proof store b :: acc
      in
      assert (Var.level store (Atom.var a) >= 0);
      match Var.reason store (Atom.var a) with
      | Some (Bcp c | Bcp_lazy (lazy c)) ->
        Log.debugf 5 (fun k->k "(@[proof.analyze.clause@ :atom %a@ :c %a@])"
                         (Atom.debug store) a (Clause.debug store) c);
        if Clause.n_atoms store c = 1 then (
          Log.debugf 5 (fun k -> k "(@[proof.analyze.old-reason@ %a@])"
                           (Atom.debug store) a);
          c
        ) else (
          assert (Atom.is_false store a);
          let r = History (c :: (Clause.fold store [] c ~f:aux)) in
          let c' = Clause.make_l store ~removable:false [Atom.neg a] r in
          Var.set_reason store (Atom.var a) (Some (Bcp c'));
          Log.debugf 5
            (fun k -> k "(@[proof.analyze.new-reason@ :atom %a@ :c %a@])"
                (Atom.debug store) a (Clause.debug store) c');
          c'
        )
      | _ ->
        error_res_f "cannot prove atom %a" (Atom.debug store) a

    let prove_unsat store conflict =
      if Clause.n_atoms store conflict = 0 then (
        conflict
      ) else (
        Log.debugf 1 (fun k -> k "(@[sat.prove-unsat@ :from %a@])" (Clause.debug store) conflict);
        let l = Clause.fold store [] conflict
            ~f:(fun acc a -> set_atom_proof store a :: acc) in
        let res = Clause.make_l store ~removable:false [] (History (conflict :: l)) in
        Log.debugf 1 (fun k -> k "(@[sat.proof-found@ %a@])" (Clause.debug store) res);
        res
      )

    let prove_atom self a =
      if Atom.is_true self a &&
         Var.level self (Atom.var a) = 0 then
        Some (set_atom_proof self a)
      else
        None

    type t = clause
    and proof_node = {
      conclusion : clause;
      step : step;
    }
    and step =
      | Hypothesis of lemma
      | Assumption
      | Lemma of lemma
      | Duplicate of t * atom list
      | Hyper_res of hyper_res_step

    and hyper_res_step = {
      hr_init: t;
      hr_steps: (atom * t) list; (* list of pivot+clause to resolve against [init] *)
    }

    let[@inline] conclusion (p:t) : clause = p

    (* find pivots for resolving [l] with [init], and also return
       the atoms of the conclusion *)
    let find_pivots store (init:clause) (l:clause list) : _ * (atom * t) list =
      Log.debugf 15
        (fun k->k "(@[proof.find-pivots@ :init %a@ :l %a@])"
            (Clause.debug store) init (Format.pp_print_list (Clause.debug store)) l);
      Clause.iter store init ~f:(Atom.mark store);
      let steps =
        List.map
          (fun c ->
             let pivot =
               match
                 Clause.atoms_iter store c
                 |> Iter.filter (fun a -> Atom.marked store (Atom.neg a))
                 |> Iter.to_list
               with
                 | [a] -> a
                 | [] ->
                   error_res_f "(@[proof.expand.pivot_missing@ %a@])" (Clause.debug store) c
                 | pivots ->
                   error_res_f "(@[proof.expand.multiple_pivots@ %a@ :pivots %a@])"
                     (Clause.debug store) c (Atom.debug_l store) pivots
             in
             Clause.iter store c ~f:(Atom.mark store); (* add atoms to result *)
             clear_var_of_ store pivot;
             Atom.abs pivot, c)
          l
      in
      (* cleanup *)
      let res = ref [] in
      let cleanup_a_ a =
        if Atom.marked store a then (
          res := a :: !res;
          clear_var_of_ store a
        )
      in
      Clause.iter store init ~f:cleanup_a_;
      List.iter (fun c -> Clause.iter store c ~f:cleanup_a_) l;
      !res, steps

    let expand store conclusion =
      Log.debugf 5 (fun k -> k "(@[sat.proof.expand@ @[%a@]@])" (Clause.debug store) conclusion);
      match Clause.premise store conclusion with
      | Lemma l ->
        { conclusion; step = Lemma l; }
      | Local ->
        { conclusion; step = Assumption; }
      | Hyp l ->
        { conclusion; step = Hypothesis l; }
      | History [] ->
        error_res_f "@[empty history for clause@ %a@]" (Clause.debug store) conclusion
      | History [c] ->
        let duplicates, res = find_dups store c in
        assert (same_lits store (Iter.of_list res) (Clause.atoms_iter store conclusion));
        { conclusion; step = Duplicate (c, duplicates) }
      | History (c :: r) ->
        let res, steps = find_pivots store c r in
        assert (same_lits store (Iter.of_list res) (Clause.atoms_iter store conclusion));
        { conclusion; step = Hyper_res {hr_init=c; hr_steps=steps};  }
      | Empty_premise -> raise Solver_intf.No_proof

    let rec res_of_hyper_res store (hr: hyper_res_step) : _ * _ * atom =
      let {hr_init=c1; hr_steps=l} = hr in
      match l with
      | [] -> assert false
      | [a, c2] -> c1, c2, a (* done *)
      | (a,c2) :: steps' ->
        (* resolve [c1] with [c2], then resolve that against [steps] *)
        let pivots, l = resolve store c1 c2 in
        assert (match pivots with [a'] -> Atom.equal a a' | _ -> false);
        let c_1_2 = Clause.make_l store ~removable:true l (History [c1; c2]) in
        res_of_hyper_res store {hr_init=c_1_2; hr_steps=steps'}

    (* Proof nodes manipulation *)
    let is_leaf = function
      | Hypothesis _
      | Assumption
      | Lemma _ -> true
      | Duplicate _
      | Hyper_res _ -> false

    let parents = function
      | Hypothesis _
      | Assumption
      | Lemma _ -> []
      | Duplicate (p, _) -> [p]
      | Hyper_res {hr_init; hr_steps} -> hr_init :: List.map snd hr_steps

    let expl = function
      | Hypothesis _ -> "hypothesis"
      | Assumption -> "assumption"
      | Lemma _ -> "lemma"
      | Duplicate _ -> "duplicate"
      | Hyper_res _ -> "hyper-resolution"

    module Tbl = Clause.Tbl

    type task =
      | Enter of t
      | Leaving of t

    let spop s = try Some (Stack.pop s) with Stack.Empty -> None

    let rec fold_aux self s h f acc =
      match spop s with
      | None -> acc
      | Some (Leaving c) ->
        Tbl.add h c true;
        fold_aux self s h f (f acc (expand self c))
      | Some (Enter c) ->
        if not (Tbl.mem h c) then begin
          Stack.push (Leaving c) s;
          let node = expand self c in
          begin match node.step with
            | Duplicate (p1, _) ->
              Stack.push (Enter p1) s
            | Hyper_res {hr_init=p1; hr_steps=l} ->
              List.iter (fun (_,p2) -> Stack.push (Enter p2) s) l;
              Stack.push (Enter p1) s;
            | Hypothesis _ | Assumption | Lemma _ -> ()
          end
        end;
        fold_aux self s h f acc

    let fold self f acc p =
      let h = Tbl.create 42 in
      let s = Stack.create () in
      Stack.push (Enter p) s;
      fold_aux self s h f acc

    let check_empty_conclusion store (p:t) =
      if Clause.n_atoms store p > 0 then (
        error_res_f "@[<2>Proof.check: non empty conclusion for clause@ %a@]"
          (Clause.debug store) p;
      )

    let check self (p:t) = fold self (fun () _ -> ()) () p
  end

  module H = (Heap.Make [@specialise]) (struct
    type store = Store.t
    type t = var
    let[@inline] cmp store i j =
      Var.weight store j < Var.weight store i (* comparison by weight *)
    let heap_idx = Var.heap_idx
    let set_heap_idx = Var.set_heap_idx
    let of_int_unsafe = Var.of_int_unsafe
  end)

  (* cause of "unsat", possibly conditional to local assumptions *)
  type unsat_cause =
    | US_local of {
        first: atom; (* assumption which was found to be proved false *)
        core: atom list; (* the set of assumptions *)
      }
    | US_false of clause (* true unsat *)

  exception E_sat
  exception E_unsat of unsat_cause
  exception UndecidedLit
  exception Restart
  exception Conflict of clause

  let var_decay : float = 1. /. 0.95
  (* inverse of the activity factor for variables *)

  let clause_decay : float = 1. /. 0.999
  (* inverse of the activity factor for clauses *)

  let restart_inc : float = 1.5
  (* multiplicative factor for restart limit *)

  let learntsize_inc : float = 1.1
  (* multiplicative factor for [learntsize_factor] at each restart *)

  (* Singleton type containing the current state *)
  type t = {
    store : store;
    (* atom/var/clause store *)

    th: theory;
    (* user defined theory *)

    store_proof: bool; (* do we store proofs? *)

    (* Clauses are simplified for efficiency purposes. In the following
       vectors, the comments actually refer to the original non-simplified
       clause. *)

    (* TODO: this should be a veci32 *)
    clauses_hyps : clause Vec.t;
    (* clauses added by the user *)

    clauses_learnt : clause Vec.t;
    (* learnt clauses (tautologies true at any time, whatever the user level) *)

    clauses_to_add : clause Vec.t;
    (* Clauses either assumed or pushed by the theory, waiting to be added. *)

    mutable unsat_at_0: clause option;
    (* conflict at level 0, if any *)

    mutable next_decisions : atom list;
    (* When the last conflict was a semantic one (mcsat),
       this stores the next decision to make;
       if some theory wants atoms to be decided on (for theory combination),
       store them here. *)

    trail : atom Vec.t;
    (* decision stack + propagated elements (atoms or assignments). *)

    var_levels : int Vec.t;
    (* decision levels in [trail]  *)

    mutable assumptions: atom Vec.t;
    (* current assumptions *)

    mutable th_head : int;
    (* Start offset in the queue {!trail} of
       unit facts not yet seen by the theory. *)
    mutable elt_head : int;
    (* Start offset in the queue {!trail} of
       unit facts to propagate, within the trail *)

    (* invariant:
       - during propagation, th_head <= elt_head
       - then, once elt_head reaches length trail, Th.assume is
         called so that th_head can catch up with elt_head
       - this is repeated until a fixpoint is reached;
       - before a decision (and after the fixpoint),
         th_head = elt_head = length trail
    *)

    order : H.t;
    (* Heap ordered by variable activity *)

    to_clear: var Vec.t;
    (* variables to unmark *)

    (* temporaries *)

    temp_atom_vec : atom Vec.t;
    temp_clause_vec : clause Vec.t;

    mutable var_incr : float;
    (* increment for variables' activity *)

    mutable clause_incr : float;
    (* increment for clauses' activity *)

    mutable on_conflict : (atom array -> unit) option;
    mutable on_decision : (atom -> unit) option;
    mutable on_new_atom: (atom -> unit) option;
    mutable on_learnt : (atom array -> unit) option;
    mutable on_gc : (atom array -> unit) option;

    mutable n_conflicts : int;
    mutable n_propagations : int;
    mutable n_decisions : int;
    mutable n_restarts : int;
  }
  type solver = t

  (* intial restart limit *)
  let restart_first = 100

  (* initial limit for the number of learnt clauses, 1/3 of initial
      number of clauses by default *)
  let learntsize_factor = 1. /. 3.

  let _nop_on_conflict (_:atom array) = ()

  (* Starting environment. *)
  let create_ ~store ~store_proof (th:theory) : t = {
    store; th;
    unsat_at_0=None;
    next_decisions = [];

    clauses_hyps = Vec.create();
    clauses_learnt = Vec.create();

    clauses_to_add = Vec.create ();
    to_clear=Vec.create();
    temp_clause_vec=Vec.create();
    temp_atom_vec=Vec.create();

    th_head = 0;
    elt_head = 0;

    trail = Vec.create ();
    var_levels = Vec.create();
    assumptions= Vec.create();

    order = H.create store;

    var_incr = 1.;
    clause_incr = 1.;
    store_proof;

    n_conflicts = 0;
    n_decisions = 0;
    n_propagations = 0;
    n_restarts = 0;

    on_conflict = None;
    on_decision= None;
    on_new_atom = None;
    on_learnt = None;
    on_gc = None;
  }

  let create
      ?on_conflict ?on_decision ?on_new_atom ?on_learnt ?on_gc
      ?(store_proof=true) ?(size=`Big)
      (th:theory) : t =
    let store = Store.create ~size () in
    let self = create_ ~store ~store_proof th in
    self.on_new_atom <- on_new_atom;
    self.on_decision <- on_decision;
    self.on_conflict <- on_conflict;
    self.on_learnt <- on_learnt;
    self.on_gc <- on_gc;
    self

  let[@inline] decision_level st = Vec.size st.var_levels

  let[@inline] nb_clauses st = Vec.size st.clauses_hyps
  let n_propagations self = self.n_propagations
  let n_decisions self = self.n_decisions
  let n_conflicts self = self.n_conflicts
  let n_restarts self = self.n_restarts

  (* Do we have a level-0 empty clause? *)
  let[@inline] check_unsat_ st =
    match st.unsat_at_0 with
    | Some c -> raise (E_unsat (US_false c))
    | None -> ()

  (* Variable and literal activity.
     Activity is used to decide on which variable to decide when propagation
     is done. Uses a heap (implemented in Iheap), to keep track of variable activity.
     To be more general, the heap only stores the variable/literal id (i.e an int).
  *)
  let[@inline] insert_var_order st (v:var) : unit =
    H.insert st.order v

  (* create a new atom, pushing it into the decision queue if needed *)
  let make_atom (self:t) ?default_pol (p:formula) : atom =
    let a = Store.alloc_atom self.store ?default_pol p in
    if Atom.level self.store a < 0 then (
      insert_var_order self (Atom.var a);
      (match self.on_new_atom with Some f -> f a | None -> ());
    ) else (
      assert (Atom.is_true self.store a || Atom.is_false self.store a);
    );
    a

  (* Rather than iterate over all the heap when we want to decrease all the
     variables/literals activity, we instead increase the value by which
     we increase the activity of 'interesting' var/lits. *)
  let[@inline] var_decay_activity st =
    st.var_incr <- st.var_incr *. var_decay

  let[@inline] clause_decay_activity st =
    st.clause_incr <- st.clause_incr *. clause_decay

  (* increase activity of [v] *)
  let var_bump_activity self v =
    let store = self.store in
    Var.set_weight store v (Var.weight store v +. self.var_incr);
    if Var.weight store v > 1e100 then (
      Store.iter_vars store
        (fun v ->
           Var.set_weight store v (Var.weight store v *. 1e-100));
      self.var_incr <- self.var_incr *. 1e-100;
    );
    if H.in_heap self.order v then (
      H.decrease self.order v
    )

  (* increase activity of clause [c] *)
  let clause_bump_activity self (c:clause) : unit =
    let store = self.store in
    Clause.set_activity store c (Clause.activity store c +. self.clause_incr);
    if Clause.activity store c > 1e20 then (
      Vec.iter
        (fun c -> Clause.set_activity store c (Clause.activity store c *. 1e-20))
        self.clauses_learnt;
      self.clause_incr <- self.clause_incr *. 1e-20
    )

  (* Simplification of clauses.

     When adding new clauses, it is desirable to 'simplify' them, i.e
     minimize the amount of literals in it, because it greatly reduces
     the search space for new watched literals during propagation.
     Additionally, we have to partition the lits, to ensure the watched
     literals (which are the first two lits of the clause) are appropriate.
     Indeed, it is better to watch true literals, and then unassigned literals.
     Watching false literals should be a last resort, and come with constraints
     (see {!add_clause}).
  *)
  exception Trivial

  (* [arr_to_list a i] converts [a.(i), ... a.(length a-1)] into a list *)
  let arr_to_list arr i : _ list =
    if i >= Array.length arr then []
    else Array.to_list (Array.sub arr i (Array.length arr - i))

  (* Eliminates atom duplicates in clauses *)
  let eliminate_duplicates store clause : clause =
    let trivial = ref false in
    let duplicates = ref [] in
    let res = ref [] in
    Clause.iter store clause
      ~f:(fun a ->
        if Atom.marked store a then duplicates := a :: !duplicates
        else (
          Atom.mark store a;
          res := a :: !res
        ));
    List.iter
      (fun a ->
         if Atom.marked_both store a then trivial := true;
         Store.clear_var store (Atom.var a))
      !res;
    if !trivial then (
      raise Trivial
    ) else if !duplicates = [] then (
      clause
    ) else (
      let removable = Clause.removable store clause in
      Clause.make_l store ~removable !res (History [clause])
    )

  (* TODO: do it in place in a vec? *)
  (* Partition literals for new clauses, into:
     - true literals (maybe makes the clause trivial if the lit is proved true at level 0)
     - unassigned literals, yet to be decided
     - false literals (not suitable to watch, those at level 0 can be removed from the clause)

     Clauses that propagated false lits are remembered to reconstruct resolution proofs.
  *)
  let partition store atoms : atom list * clause list =
    let rec partition_aux trues unassigned falses history i =
      if i >= Array.length atoms then (
        trues @ unassigned @ falses, history
      ) else (
        let a = atoms.(i) in
        if Atom.is_true store a then (
          let l = Atom.level store a in
          if l = 0 then
            raise_notrace Trivial (* Atom var true at level 0 gives a trivially true clause *)
          else
            (a :: trues) @ unassigned @ falses @
            (arr_to_list atoms (i + 1)), history
        ) else if Atom.is_false store a then (
          let l = Atom.level store a in
          if l = 0 then (
            match Atom.reason store a with
            | Some (Bcp cl | Bcp_lazy (lazy cl)) ->
              partition_aux trues unassigned falses (cl :: history) (i + 1)
            (* Atom var false at level 0 can be eliminated from the clause,
               but we need to kepp in mind that we used another clause to simplify it. *)
            (* TODO: get a proof of the propagation. *)
            | None | Some Decision -> assert false
            (* The var must have a reason, and it cannot be a decision/assumption,
               since its level is 0. *)
          ) else (
            partition_aux trues unassigned (a::falses) history (i + 1)
          )
        ) else (
          partition_aux trues (a::unassigned) falses history (i + 1)
        )
      )
    in
    partition_aux [] [] [] [] 0


  (* Making a decision.
     Before actually creatig a new decision level, we check that
     all propagations have been done and propagated to the theory,
     i.e that the theoriy state indeed takes into account the whole
     stack of literals
     i.e we have indeed reached a propagation fixpoint before making
     a new decision *)
  let new_decision_level st =
    assert (st.th_head = Vec.size st.trail);
    assert (st.elt_head = Vec.size st.trail);
    Vec.push st.var_levels (Vec.size st.trail);
    Plugin.push_level st.th;
    ()

  (* Attach/Detach a clause.

     Atom clause is attached (to its watching lits) when it is first added,
     either because it is assumed or learnt.

  *)
  let attach_clause (self:t) c =
    let store = self.store in
    assert (not @@ Clause.attached store c);
    Log.debugf 20 (fun k -> k "(@[sat.attach-clause@ %a@])" (Clause.debug store) c);
    (* TODO: change when watchlist are updated *)
    Vec.push (Atom.watched store (Atom.neg (Clause.atoms_a store c).(0))) c;
    Vec.push (Atom.watched store (Atom.neg (Clause.atoms_a store c).(1))) c;
    Clause.set_attached store c true;
    ()

  (* Backtracking.
     Used to backtrack, i.e cancel down to [lvl] excluded,
     i.e we want to go back to the state the solver was in
         when decision level [lvl] was created. *)
  let cancel_until (self:t) lvl =
    let store = self.store in
    assert (lvl >= 0);
    (* Nothing to do if we try to backtrack to a non-existent level. *)
    if decision_level self <= lvl then (
      Log.debugf 20 (fun k -> k "(@[sat.cancel-until.nop@ :already-at-level <= %d@])" lvl)
    ) else (
      Log.debugf 5 (fun k -> k "(@[sat.cancel-until %d@])" lvl);
      (* We set the head of the solver and theory queue to what it was. *)
      let head = ref (Vec.get self.var_levels lvl) in
      self.elt_head <- !head;
      self.th_head <- !head;
      (* Now we need to cleanup the vars that are not valid anymore
         (i.e to the right of elt_head in the queue. *)
      for c = self.elt_head to Vec.size self.trail - 1 do
        let a = Vec.get self.trail c in
        (* Atom literal is unassigned, we nedd to add it back to
           the heap of potentially assignable literals, unless it has
           a level lower than [lvl], in which case we just move it back. *)
        (* Atom variable is not true/false anymore, one of two things can happen: *)
        if Atom.level store a <= lvl then (
          (* It is a late propagation, which has a level
             lower than where we backtrack, so we just move it to the head
             of the queue, to be propagated again. *)
          Vec.set self.trail !head a;
          head := !head + 1
        ) else (
          (* it is a result of bolean propagation, or a semantic propagation
             with a level higher than the level to which we backtrack,
             in that case, we simply unset its value and reinsert it into the heap. *)
          Atom.set_is_true store a false;
          Atom.set_is_true store (Atom.neg a) false;
          Var.set_level store (Atom.var a) (-1);
          Var.set_reason store (Atom.var a) None;
          insert_var_order self (Atom.var a)
        )
      done;
      (* Recover the right theory state. *)
      let n = decision_level self - lvl in
      assert (n>0);
      (* Resize the vectors according to their new size. *)
      Vec.shrink self.trail !head;
      Vec.shrink self.var_levels lvl;
      Plugin.pop_levels self.th n;
      self.next_decisions <- [];
    );
    ()

  let pp_unsat_cause self out = function
    | US_local {first=_; core} ->
      Format.fprintf out "(@[unsat-cause@ :false-assumptions %a@])"
        (Format.pp_print_list (Atom.pp self.store)) core
    | US_false c ->
      Format.fprintf out "(@[unsat-cause@ :false %a@])" (Clause.debug self.store) c

  (* Unsatisfiability is signaled through an exception, since it can happen
     in multiple places (adding new clauses, or solving for instance). *)
  let report_unsat self (us:unsat_cause) : _ =
    Log.debugf 3 (fun k -> k "(@[sat.unsat-conflict@ %a@])" (pp_unsat_cause self) us);
    let us = match us with
      | US_false c ->
        let c = if self.store_proof then Proof.prove_unsat self.store c else c in
        self.unsat_at_0 <- Some c;
        US_false c
      | _ -> us
    in
    raise (E_unsat us)

  (* TODO: remove when we use DRUP *)
  (* Simplification of boolean propagation reasons.
     When doing boolean propagation *at level 0*, it can happen
     that the clause cl, which propagates a formula, also contains
     other formulas, but has been simplified. in which case, we
     need to rebuild a clause with correct history, in order to
     be able to build a correct proof at the end of proof search. *)
  let simpl_reason (self:t) (r:reason) : reason =
    match r with
    | (Bcp cl | Bcp_lazy (lazy cl)) as r ->
      let l, history = partition self.store (Clause.atoms_a self.store cl) in
      begin match l with
        | [_] ->
          if history = [] then (
            (* no simplification has been done, so [cl] is actually a clause with only
               [a], so it is a valid reason for propagating [a]. *)
            r
          ) else (
            (* Clauses in [history] have been used to simplify [cl] into a clause [tmp_cl]
               with only one formula (which is [a]). So we explicitly create that clause
               and set it as the cause for the propagation of [a], that way we can
               rebuild the whole resolution tree when we want to prove [a]. *)
            let removable = Clause.removable self.store cl in
            let c' =
              Clause.make_l self.store ~removable l (History (cl :: history))
            in
            Log.debugf 3
              (fun k -> k "(@[<hv>sat.simplified-reason@ %a@ %a@])"
                  (Clause.debug self.store) cl (Clause.debug self.store) c');
            Bcp c'
          )
        | _ ->
          Log.debugf 0
            (fun k ->
               k "(@[<v2>sat.simplify-reason.failed@ :at %a@ %a@]"
                 (Vec.pp ~sep:"" (Atom.debug self.store)) (Vec.of_list l)
                 (Clause.debug self.store) cl);
          assert false
      end
    | Decision as r -> r

  (* Boolean propagation.
     Wrapper function for adding a new propagated formula. *)
  let enqueue_bool (self:t) a ~level:lvl reason : unit =
    let store = self.store in
    if Atom.is_false store a then (
      Log.debugf 0
        (fun k->k "(@[sat.error.trying to enqueue a false literal %a@])" (Atom.debug store) a);
      assert false
    );
    assert (not (Atom.is_true store a) &&
            Atom.level store a < 0 &&
            Atom.reason store a == None && lvl >= 0);
    let reason =
      if lvl > 0 then reason
      else simpl_reason self reason
    in
    Atom.set_is_true store a true;
    Var.set_level store (Atom.var a) lvl;
    Var.set_reason store (Atom.var a) (Some reason);
    Vec.push self.trail a;
    Log.debugf 20
      (fun k->k "(@[sat.enqueue[%d]@ %a@])"
          (Vec.size self.trail) (Atom.debug store) a);
    ()

  (* swap elements of array *)
  let[@inline] swap_arr a i j =
    if i<>j then (
      let tmp = a.(i) in
      a.(i) <- a.(j);
      a.(j) <- tmp;
    )

  (* move atoms assigned at high levels first *)
  let put_high_level_atoms_first (store:store) (arr:atom array) : unit =
    Array.iteri
      (fun i a ->
         if i>0 && Atom.level store a > Atom.level store arr.(0) then (
           (* move first to second, [i]-th to first, second to [i] *)
           if i=1 then (
             swap_arr arr 0 1;
           ) else (
             let tmp = arr.(1) in
             arr.(1) <- arr.(0);
             arr.(0) <- arr.(i);
             arr.(i) <- tmp;
           );
         ) else if i>1 &&
                   Atom.level store a > Atom.level store arr.(1)
         then (
           swap_arr arr 1 i;
         ))
      arr

  (* find which level to backtrack to, given a conflict clause
     and a boolean stating whether it is
     a UIP ("Unique Implication Point")
     precond: the atom list is sorted by decreasing decision level *)
  let backtrack_lvl (self:t) (arr: atom array) : int * bool =
    let store = self.store in
    if Array.length arr <= 1 then (
      0, true
    ) else (
      let a = arr.(0) in
      let b = arr.(1) in
      assert (Atom.level store a > 0);
      if Atom.level store a > Atom.level store b then (
        (* backtrack below [a], so we can propagate [not a] *)
        Atom.level store b, true
      ) else (
        assert (Atom.level store a = Atom.level store b);
        assert (Atom.level store a >= 0);
        max (Atom.level store a - 1) 0, false
      )
    )

  (* result of conflict analysis, containing the learnt clause and some
     additional info.

     invariant: cr_history's order matters, as its head is later used
     during pop operations to determine the origin of a clause/conflict
     (boolean conflict i.e hypothesis, or theory lemma) *)
  type conflict_res = {
    cr_backtrack_lvl : int; (* level to backtrack to *)
    cr_learnt: atom array; (* lemma learnt from conflict *)
    cr_history: clause array; (* justification *)
    cr_is_uip: bool; (* conflict is UIP? *)
  }

  (* conflict analysis, starting with top of trail and conflict clause *)
  let analyze (self:t) c_clause : conflict_res =
    let store = self.store in

    let to_unmark = self.to_clear in (* for cleanup *)
    Vec.clear to_unmark;
    let learnt = self.temp_atom_vec in
    Vec.clear learnt;
    let history = self.temp_clause_vec in
    Vec.clear history;

    (* loop variables *)
    let pathC  = ref 0 in
    let continue = ref true in
    let blevel = ref 0 in
    let c = ref (Some c_clause) in (* current clause to analyze/resolve *)
    let tr_ind = ref (Vec.size self.trail - 1) in (* pointer in trail *)

    (* conflict level *)
    assert (decision_level self > 0);
    let conflict_level =
      if Plugin.has_theory then (
        Clause.fold store 0 c_clause
          ~f:(fun acc p -> max acc (Atom.level store p))
      ) else (
        decision_level self
      )
    in
    Log.debugf 30
      (fun k -> k "(@[sat.analyze-conflict@ :c-level %d@ :clause %a@])"
          conflict_level (Clause.debug store) c_clause);

    while !continue do
      begin match !c with
        | None ->
          Log.debug 30
            "(@[sat.analyze-conflict: skipping resolution for semantic propagation@])"
        | Some clause ->
          Log.debugf 30
            (fun k->k"(@[sat.analyze-conflict.resolve@ %a@])" (Clause.debug store) clause);
          if Clause.removable store clause then (
            clause_bump_activity self clause;
          );
          Vec.push history clause;
          (* visit the current predecessors *)
          let atoms = Clause.atoms_a store clause in
          for j = 0 to Array.length atoms - 1 do
            let q = atoms.(j) in
            assert (Atom.is_true store q ||
                    Atom.is_false store q &&
                    Atom.level store q >= 0); (* unsure? *)
            if Atom.level store q <= 0 then (
              assert (Atom.is_false store q);
              match Atom.reason store q with
              | Some (Bcp cl | Bcp_lazy (lazy cl)) ->
                Vec.push history cl
              | Some Decision | None -> assert false
            );
            if not (Var.marked store (Atom.var q)) then (
              Var.mark store (Atom.var q);
              Vec.push to_unmark (Atom.var q);
              if Atom.level store q > 0 then (
                var_bump_activity self (Atom.var q);
                if Atom.level store q >= conflict_level then (
                  incr pathC;
                ) else (
                  Vec.push learnt q;
                  blevel := max !blevel (Atom.level store q)
                )
              )
            )
          done
      end;

      (* look for the next node to expand *)
      while
        let a = Vec.get self.trail !tr_ind in
        Log.debugf 30
          (fun k -> k "(@[sat.analyze-conflict.at-trail-elt@ %a@])" (Atom.debug store) a);
        (not (Var.marked store (Atom.var a))) ||
        (Atom.level store a < conflict_level)
      do
        decr tr_ind;
      done;
      let p = Vec.get self.trail !tr_ind in
      decr pathC;
      decr tr_ind;
      match !pathC, Atom.reason store p with
      | 0, _ ->
        continue := false;
        Vec.push learnt (Atom.neg p)
      | n, Some (Bcp cl | Bcp_lazy (lazy cl)) ->
        assert (n > 0);
        assert (Atom.level store p >= conflict_level);
        c := Some cl
      | _, (None | Some Decision) -> assert false
    done;

    Vec.iter (Store.clear_var store) to_unmark;
    Vec.clear to_unmark;

    (* put high-level literals first, so that:
       - they make adequate watch lits
       - the first literal is the UIP, if any *)
    let cr_learnt = Vec.to_array learnt in
    Vec.clear learnt;
    Array.sort (fun p q -> compare (Atom.level store q) (Atom.level store p)) cr_learnt;

    let cr_history = Vec.to_array history in
    Vec.clear history;

    (* put_high_level_atoms_first a; *)
    let level, is_uip = backtrack_lvl self cr_learnt in
    { cr_backtrack_lvl = level;
      cr_learnt;
      cr_history;
      cr_is_uip = is_uip;
    }

  (* add the learnt clause to the clause database, propagate, etc. *)
  let record_learnt_clause (self:t) (confl:clause) (cr:conflict_res): unit =
    let store = self.store in
    let proof =
      if self.store_proof
      then History (Array.to_list cr.cr_history)
      else Empty_premise in
    begin match cr.cr_learnt with
      | [| |] -> assert false
      | [|fuip|] ->
        assert (cr.cr_backtrack_lvl = 0 && decision_level self = 0);
        if Atom.is_false store fuip then (
          (* incompatible at level 0 *)
          report_unsat self (US_false confl)
        ) else (
          let uclause =
            Clause.make_a store ~removable:true cr.cr_learnt proof  in
          (* no need to attach [uclause], it is true at level 0 *)
          enqueue_bool self fuip ~level:0 (Bcp uclause)
        )
      | _ ->
        let fuip = cr.cr_learnt.(0) in
        let lclause = Clause.make_a store ~removable:true cr.cr_learnt proof in
        if Clause.n_atoms store lclause > 2 then (
          Vec.push self.clauses_learnt lclause; (* potentially gc'able *)
        );
        attach_clause self lclause;
        clause_bump_activity self lclause;
        (match self.on_learnt with Some f -> f cr.cr_learnt | None -> ());
        assert (cr.cr_is_uip);
        enqueue_bool self fuip ~level:cr.cr_backtrack_lvl (Bcp lclause)
    end;
    var_decay_activity self;
    clause_decay_activity self

  (* process a conflict:
     - learn clause
     - backtrack
     - report unsat if conflict at level 0
  *)
  let add_boolean_conflict (self:t) (confl:clause): unit =
    let store = self.store in
    Log.debugf 5 (fun k -> k "(@[sat.add-bool-conflict@ %a@])" (Clause.debug store) confl);
    self.next_decisions <- [];
    assert (decision_level self >= 0);
    if decision_level self = 0 ||
       Clause.for_all store confl ~f:(fun a -> Atom.level store a <= 0) then (
      (* Top-level conflict *)
      report_unsat self (US_false confl);
    );
    let cr = analyze self confl in
    cancel_until self (max cr.cr_backtrack_lvl 0);
    record_learnt_clause self confl cr

  (* Get the correct vector to insert a clause in. *)
  let[@inline] add_clause_to_vec self c =
    if Clause.removable self.store c then (
      Vec.push self.clauses_learnt c
    ) else (
      Vec.push self.clauses_hyps c
    )

  (* Add a new clause, simplifying, propagating, and backtracking if
     the clause is false in the current trail *)
  let add_clause_ (self:t) (init:clause) : unit =
    let store = self.store in
    Log.debugf 30 (fun k -> k "(@[sat.add-clause@ @[<hov>%a@]@])" (Clause.debug store) init);
    (* Insertion of new lits is done before simplification. Indeed, else a lit in a
       trivial clause could end up being not decided on, which is a bug. *)
    Clause.iter store init ~f:(fun x -> insert_var_order self (Atom.var x));
    try
      let c = eliminate_duplicates store init in
      Log.debugf 30 (fun k -> k "(@[sat.dups-removed@ %a@])" (Clause.debug store) c);
      let atoms, history = partition store (Clause.atoms_a store c) in
      let clause =
        if history = [] then (
          (* just update order of atoms *)
          let c_atoms = Clause.atoms_a store c in
          List.iteri (fun i a -> c_atoms.(i) <- a) atoms;
          c
        ) else (
          let proof = if self.store_proof then History (c::history) else Empty_premise in
          let removable = Clause.removable store c in
          Clause.make_l store ~removable atoms proof
        )
      in
      assert (Clause.removable store clause = Clause.removable store init);
      Log.debugf 5 (fun k->k "(@[sat.new-clause@ @[<hov>%a@]@])" (Clause.debug store) clause);
      match atoms with
      | [] ->
        report_unsat self @@ US_false clause
      | [a]   ->
        cancel_until self 0;
        if Atom.is_false store a then (
          (* cannot recover from this *)
          report_unsat self @@ US_false clause
        ) else if Atom.is_true store a then (
          () (* atom is already true, nothing to do *)
        ) else (
          Log.debugf 40
            (fun k->k "(@[sat.add-clause.unit-clause@ :propagating %a@])" (Atom.debug store) a);
          add_clause_to_vec self clause;
          enqueue_bool self a ~level:0 (Bcp clause)
        )
      | a::b::_ ->
        add_clause_to_vec self clause;
        if Atom.is_false store a then (
          (* Atom need to be sorted in decreasing order of decision level,
             or we might watch the wrong literals. *)
          put_high_level_atoms_first store (Clause.atoms_a store clause);
          attach_clause self clause;
          add_boolean_conflict self clause
        ) else (
          attach_clause self clause;
          if Atom.is_false store b &&
             not (Atom.is_true store a) &&
             not (Atom.is_false store a) then (
            let lvl = List.fold_left (fun m a -> max m (Atom.level store a)) 0 atoms in
            cancel_until self lvl;
            enqueue_bool self a ~level:lvl (Bcp clause)
          )
        )
    with Trivial ->
      Log.debugf 5
        (fun k->k "(@[sat.add-clause@ :ignore-trivial @[%a@]@])" (Clause.debug store) init)

  let[@inline never] flush_clauses_ st =
    while not @@ Vec.is_empty st.clauses_to_add do
      let c = Vec.pop_exn st.clauses_to_add in
      add_clause_ st c
    done

  let[@inline] flush_clauses st =
    if not @@ Vec.is_empty st.clauses_to_add then flush_clauses_ st

  type watch_res =
    | Watch_kept
    | Watch_removed

  (* boolean propagation.
     [a] is the false atom, one of [c]'s two watch literals
     [i] is the index of [c] in [a.watched]
     @return whether [c] was removed from [a.watched]
  *)
  let propagate_in_clause (self:t) (a:atom) (c:clause) (i:int): watch_res =
    let store = self.store in
    let atoms = Clause.atoms_a store c in
    let first = atoms.(0) in
    if first = Atom.neg a then (
      (* false lit must be at index 1 *)
      atoms.(0) <- atoms.(1);
      atoms.(1) <- first
    ) else (
      assert (Atom.neg a = atoms.(1))
    );
    let first = atoms.(0) in
    if Atom.is_true store first then (
      Watch_kept (* true clause, keep it in watched *)
    ) else (
      try (* look for another watch lit *)
        for k = 2 to Array.length atoms - 1 do
          let ak = atoms.(k) in
          if not (Atom.is_false store ak) then (
            (* watch lit found: update and exit *)
            atoms.(1) <- ak;
            atoms.(k) <- Atom.neg a;
            (* remove [c] from [a.watched], add it to [ak.neg.watched] *)
            Vec.push (Atom.watched store (Atom.neg ak)) c;
            assert (Vec.get (Atom.watched store a) i == c);
            Vec.fast_remove (Atom.watched store a) i;
            raise_notrace Exit
          )
        done;
        (* no watch lit found *)
        if Atom.is_false store first then (
          (* clause is false *)
          self.elt_head <- Vec.size self.trail;
          raise_notrace (Conflict c)
        ) else (
          self.n_propagations <- 1 + self.n_propagations;
          enqueue_bool self first ~level:(decision_level self) (Bcp c)
        );
        Watch_kept
      with Exit ->
        Watch_removed
    )

  (* propagate atom [a], which was just decided. This checks every
     clause watching [a] to see if the clause is false, unit, or has
     other possible watches
     @param res the optional conflict clause that the propagation might trigger *)
  let propagate_atom (self:t) a : unit =
    let store = self.store in
    let watched = Atom.watched store a in
    let rec aux i =
      if i >= Vec.size watched then ()
      else (
        let c = Vec.get watched i in
        assert (Clause.attached store c);
        let j =
          if Clause.dead store c then (
            Vec.fast_remove watched i;
            i
          ) else (
            match propagate_in_clause self a c i with
            | Watch_kept -> i+1
            | Watch_removed -> i (* clause at this index changed *)
          )
        in
        aux j
      )
    in
    aux 0

  exception Th_conflict of Clause.t

  let[@inline] slice_get st i = Vec.get st.trail i

  let acts_add_clause self ?(keep=false) (l:formula list) (lemma:lemma): unit =
    let atoms = List.rev_map (make_atom self) l in
    let removable = not keep in
    let c = Clause.make_l self.store ~removable atoms (Lemma lemma) in
    Log.debugf 5 (fun k->k "(@[sat.th.add-clause@ %a@])" (Clause.debug self.store) c);
    Vec.push self.clauses_to_add c

  let acts_add_decision_lit (self:t) (f:formula) (sign:bool) : unit =
    let store = self.store in
    let a = make_atom self f in
    let a = if sign then a else Atom.neg a in
    if not (Atom.has_value store a) then (
      Log.debugf 10 (fun k->k "(@[sat.th.add-decision-lit@ %a@])" (Atom.debug store) a);
      self.next_decisions <- a :: self.next_decisions
    )

  let acts_raise self (l:formula list) proof : 'a =
    let atoms = List.rev_map (make_atom self) l in
    (* conflicts can be removed *)
    let c = Clause.make_l self.store ~removable:true atoms (Lemma proof) in
    Log.debugf 5 (fun k->k "(@[@{<yellow>sat.th.raise-conflict@}@ %a@])"
                     (Clause.debug self.store) c);
    raise_notrace (Th_conflict c)

  let check_consequence_lits_false_ self l : unit =
    let store = self.store in
    match List.find (Atom.is_true store) l with
    | a ->
      invalid_argf
        "slice.acts_propagate:@ Consequence should contain only true literals, but %a isn't"
        (Atom.debug store) (Atom.neg a)
    | exception Not_found -> ()

  let acts_propagate (self:t) f expl =
    let store = self.store in
    match expl with
    | Solver_intf.Consequence mk_expl ->
      let p = make_atom self f in
      if Atom.is_true store p then ()
      else if Atom.is_false store p then (
        let lits, proof = mk_expl() in
        let l = List.rev_map (fun f -> Atom.neg @@ make_atom self f) lits in
        check_consequence_lits_false_ self l;
        let c = Clause.make_l store ~removable:true (p :: l) (Lemma proof) in
        raise_notrace (Th_conflict c)
      ) else (
        insert_var_order self (Atom.var p);
        let c = lazy (
          let lits, proof = mk_expl () in
          let l = List.rev_map (fun f -> Atom.neg @@ make_atom self f) lits in
          (* note: we can check that invariant here in the [lazy] block,
             as conflict analysis will run in an environment where
             the literals should be true anyway, since it's an extension of the
             current trail
             (otherwise the propagated lit would have been backtracked and
             discarded already.) *)
          check_consequence_lits_false_ self l;
          Clause.make_l store ~removable:true (p :: l) (Lemma proof)
        ) in
        let level = decision_level self in
        self.n_propagations <- 1 + self.n_propagations;
        enqueue_bool self p ~level (Bcp_lazy c)
      )

  let[@specialise] acts_iter self ~full head f : unit =
    for i = (if full then 0 else head) to Vec.size self.trail-1 do
      let a = Vec.get self.trail i in
      f (Atom.lit self.store a);
    done

  let eval_atom_ self a =
    if Atom.is_true self.store a then Solver_intf.L_true
    else if Atom.is_false self.store a then Solver_intf.L_false
    else Solver_intf.L_undefined

  let[@inline] acts_eval_lit self (f:formula) : Solver_intf.lbool =
    let a = make_atom self f in
    eval_atom_ self a

  let[@inline] acts_mk_lit self ?default_pol f : unit =
    ignore (make_atom ?default_pol self f : atom)

  let[@inline] current_slice st : _ Solver_intf.acts =
    let module M = struct
      type nonrec proof = lemma
      type nonrec formula = formula
      let iter_assumptions=acts_iter st ~full:false st.th_head
      let eval_lit= acts_eval_lit st
      let mk_lit=acts_mk_lit st
      let add_clause = acts_add_clause st
      let propagate = acts_propagate st
      let raise_conflict c pr=acts_raise st c pr
      let add_decision_lit=acts_add_decision_lit st
    end in
    (module M)

  (* full slice, for [if_sat] final check *)
  let[@inline] full_slice st : _ Solver_intf.acts =
    let module M = struct
      type nonrec proof = lemma
      type nonrec formula = formula
      let iter_assumptions=acts_iter st ~full:true st.th_head
      let eval_lit= acts_eval_lit st
      let mk_lit=acts_mk_lit st
      let add_clause = acts_add_clause st
      let propagate = acts_propagate st
      let raise_conflict c pr=acts_raise st c pr
      let add_decision_lit=acts_add_decision_lit st
    end in
    (module M)

  (* Assert that the conflict is indeeed a conflict *)
  let check_is_conflict_ self (c:Clause.t) : unit =
    if not @@ Clause.for_all self.store c ~f:(Atom.is_false self.store) then (
      Log.debugf 0 (fun k->k"conflict should be false: %a" (Clause.debug self.store) c);
      assert false
    )

  (* some boolean literals were decided/propagated within Msat. Now we
     need to inform the theory of those assumptions, so it can do its job.
     @return the conflict clause, if the theory detects unsatisfiability *)
  let rec theory_propagate self : clause option =
    assert (self.elt_head = Vec.size self.trail);
    assert (self.th_head <= self.elt_head);
    if self.th_head = self.elt_head then (
      None (* fixpoint/no propagation *)
    ) else (
      let slice = current_slice self in
      self.th_head <- self.elt_head; (* catch up *)
      match Plugin.partial_check self.th slice with
      | () ->
        flush_clauses self;
        propagate self
      | exception Th_conflict c ->
        check_is_conflict_ self c;
        Clause.iter self.store c ~f:(fun a -> insert_var_order self (Atom.var a));
        Some c
    )

  (* fixpoint between boolean propagation and theory propagation
     @return a conflict clause, if any *)
  and propagate (st:t) : clause option =
    (* First, treat the stack of lemmas added by the theory, if any *)
    flush_clauses st;
    (* Now, check that the situation is sane *)
    assert (st.elt_head <= Vec.size st.trail);
    if st.elt_head = Vec.size st.trail then (
      theory_propagate st
    ) else (
      match
        while st.elt_head < Vec.size st.trail do
          let a = Vec.get st.trail st.elt_head in
          propagate_atom st a;
          st.elt_head <- st.elt_head + 1;
        done;
      with
      | () -> theory_propagate st
      | exception Conflict c -> Some c
    )

  (* compute unsat core from assumption [a] *)
  let analyze_final (self:t) (a:atom) : atom list =
    let store = self.store in
    Log.debugf 5 (fun k->k "(@[sat.analyze-final@ :lit %a@])" (Atom.debug store) a);
    assert (Atom.is_false store a);
    let core = ref [a] in
    let idx = ref (Vec.size self.trail - 1) in
    Var.mark store (Atom.var a);
    let seen = ref [Atom.var a] in
    while !idx >= 0 do
      let a' = Vec.get self.trail !idx in
      if Var.marked store (Atom.var a') then (
        match Atom.reason store a' with
        | Some Decision -> core := a' :: !core
        | Some (Bcp c | Bcp_lazy (lazy c)) ->
          Clause.iter store c
            ~f:(fun a ->
               let v = Atom.var a in
               if not (Var.marked store v) then (
                 seen := v :: !seen;
                 Var.mark store v;
               ))
        | None -> ()
      );
      decr idx
    done;
    List.iter (Var.unmark store) !seen;
    Log.debugf 5 (fun k->k "(@[sat.analyze-final.done@ :core %a@])"
                     (Format.pp_print_list (Atom.debug store)) !core);
    !core

  (* TODO: compact regularly to remove dead clauses *)
  (* remove some learnt clauses. *)
  let reduce_db (st:t) (n_of_learnts: int) : unit =
    let store = st.store in
    let v = st.clauses_learnt in
    Log.debugf 3 (fun k->k "(@[sat.gc.start :keep %d :out-of %d@])" n_of_learnts (Vec.size v));
    assert (Vec.size v > n_of_learnts);
    (* sort by decreasing activity *)
    Vec.sort v (fun c1 c2 -> compare (Clause.activity store c2) (Clause.activity store c1));
    let n_collected = ref 0 in
    while Vec.size v > n_of_learnts do
      let c = Vec.pop_exn v in
      assert (Clause.removable store c);
      Clause.dealloc store c;
      incr n_collected;
    done;
    Log.debugf 3 (fun k->k "(@[sat.gc.done :collected %d@])" !n_collected);
    ()

  (* Decide on a new literal, and enqueue it into the trail *)
  let rec pick_branch_aux self atom : unit =
    let v = Atom.var atom in
    if Var.level self.store v >= 0 then (
      assert (Atom.is_true self.store (Atom.pa v) ||
              Atom.is_true self.store (Atom.na v));
      pick_branch_lit self
    ) else (
      new_decision_level self;
      let current_level = decision_level self in
      enqueue_bool self atom ~level:current_level Decision;
      self.n_decisions <- 1 + self.n_decisions;
      (match self.on_decision with Some f -> f atom | None -> ());
    )

  and pick_branch_lit self : unit =
    match self.next_decisions with
    | atom :: tl ->
      self.next_decisions <- tl;
      pick_branch_aux self atom
    | [] when decision_level self < Vec.size self.assumptions ->
      (* use an assumption *)
      let a = Vec.get self.assumptions (decision_level self) in
      if Atom.is_true self.store a then (
        new_decision_level self; (* pseudo decision level, [a] is already true *)
        pick_branch_lit self
      ) else if Atom.is_false self.store a then (
        (* root conflict, find unsat core *)
        let core = analyze_final self a in
        raise (E_unsat (US_local {first=a; core}))
      ) else (
        pick_branch_aux self a
      )
    | [] ->
      begin match H.remove_min self.order with
        | v ->
          pick_branch_aux self
            (if Var.default_pol self.store v then Atom.pa v else Atom.na v)
        | exception Not_found -> raise_notrace E_sat
      end

  (* do some amount of search, until the number of conflicts or clause learnt
     reaches the given parameters *)
  let search (st:t) n_of_conflicts n_of_learnts : unit =
    Log.debugf 3
      (fun k->k "(@[sat.search@ :n-conflicts %d@ :n-learnt %d@])" n_of_conflicts n_of_learnts);
    let conflictC = ref 0 in
    while true do
      match propagate st with
      | Some confl -> (* Conflict *)
        incr conflictC;
        (* When the theory has raised Unsat, add_boolean_conflict
           might 'forget' the initial conflict clause, and only add the
           analyzed backtrack clause. So in those case, we use add_clause
           to make sure the initial conflict clause is also added. *)
        if Clause.attached st.store confl then (
          add_boolean_conflict st confl
        ) else (
          add_clause_ st confl
        );
        st.n_conflicts <- 1 + st.n_conflicts;
        (match st.on_conflict with Some f -> f (Clause.atoms_a st.store confl) | None -> ());

      | None -> (* No Conflict *)
        assert (st.elt_head = Vec.size st.trail);
        assert (st.elt_head = st.th_head);
        if n_of_conflicts > 0 && !conflictC >= n_of_conflicts then (
          Log.debug 1 "(sat.restarting)";
          cancel_until st 0;
          st.n_restarts <- 1 + st.n_restarts;
          raise_notrace Restart
        );
        (* if decision_level() = 0 then simplify (); *)

        if n_of_learnts > 0 &&
           Vec.size st.clauses_learnt - Vec.size st.trail > n_of_learnts then (
          reduce_db st n_of_learnts;
        );

        pick_branch_lit st
    done

  let eval_level (self:t) (a:atom) =
    let lvl = Atom.level self.store a in
    if Atom.is_true self.store a then (
      assert (lvl >= 0);
      true, lvl
    ) else if Atom.is_false self.store a then (
      false, lvl
    ) else (
      raise UndecidedLit
    )

  let[@inline] eval st lit = fst @@ eval_level st lit

  let[@inline] unsat_conflict st = st.unsat_at_0

  (* fixpoint of propagation and decisions until a model is found, or a
     conflict is reached *)
  let solve_ (self:t) : unit =
    Log.debugf 5 (fun k->k "(@[sat.solve :assms %d@])" (Vec.size self.assumptions));
    check_unsat_ self;
    try
      flush_clauses self; (* add initial clauses *)
      let n_of_conflicts = ref (float_of_int restart_first) in
      let n_of_learnts = ref ((float_of_int (nb_clauses self)) *. learntsize_factor) in
      while true do
        begin try
            search self (int_of_float !n_of_conflicts) (int_of_float !n_of_learnts)
          with
          | Restart ->
            n_of_conflicts := !n_of_conflicts *. restart_inc;
            n_of_learnts   := !n_of_learnts *. learntsize_inc
          | E_sat ->
            assert (self.elt_head = Vec.size self.trail &&
                    Vec.is_empty self.clauses_to_add &&
                    self.next_decisions=[]);
            begin match Plugin.final_check self.th (full_slice self) with
              | () ->
                if self.elt_head = Vec.size self.trail &&
                   Vec.is_empty self.clauses_to_add &&
                   self.next_decisions = []
                then (
                  raise_notrace E_sat
                );
                (* otherwise, keep on *)
                flush_clauses self;
              | exception Th_conflict c ->
                check_is_conflict_ self c;
                Clause.iter self.store c
                  ~f:(fun a -> insert_var_order self (Atom.var a));
                Log.debugf 5 (fun k -> k "(@[sat.theory-conflict-clause@ %a@])"
                                 (Clause.debug self.store) c);
                self.n_conflicts <- 1 + self.n_conflicts;
                (match self.on_conflict with
                   Some f -> f (Clause.atoms_a self.store c) | None -> ());
                Vec.push self.clauses_to_add c;
                flush_clauses self;
            end;
        end
      done
    with E_sat -> ()

  let assume self cnf lemma : unit =
    List.iter
      (fun l ->
         let atoms = List.rev_map (make_atom self) l in
         let c = Clause.make_l self.store ~removable:false atoms (Hyp lemma) in
         Log.debugf 10 (fun k -> k "(@[sat.assume-clause@ @[<hov 2>%a@]@])"
                           (Clause.debug self.store) c);
         Vec.push self.clauses_to_add c)
      cnf

  (* Check satisfiability *)
  let check_clause self c =
    let res = Clause.exists self.store c ~f:(Atom.is_true self.store) in
    if not res then (
      Log.debugf 30
        (fun k -> k "(@[sat.check-clause@ :not-satisfied @[<hov>%a@]@])"
            (Clause.debug self.store) c);
      false
    ) else
      true

  let check_vec self v = Vec.for_all (check_clause self) v
  let check self : bool =
    Vec.is_empty self.clauses_to_add &&
    check_vec self self.clauses_hyps &&
    check_vec self self.clauses_learnt

  let[@inline] theory st = st.th
  let[@inline] store st = st.store

  (* Result type *)
  type res =
    | Sat of Formula.t Solver_intf.sat_state
    | Unsat of (atom,clause,Proof.t) Solver_intf.unsat_state

  let pp_all self lvl status =
    Log.debugf lvl
      (fun k -> k
          "(@[<v>sat.full-state :res %s - Full summary:@,@[<hov 2>Trail:@\n%a@]@,\
           @[<hov 2>Hyps:@\n%a@]@,@[<hov 2>Lemmas:@\n%a@]@,@]@."
          status
          (Vec.pp ~sep:"" @@ Atom.debug self.store) self.trail
          (Vec.pp ~sep:"" @@ Clause.debug self.store) self.clauses_hyps
          (Vec.pp ~sep:"" @@ Clause.debug self.store) self.clauses_learnt)

  let mk_sat (self:t) : Formula.t Solver_intf.sat_state =
    pp_all self 99 "SAT";
    let t = self.trail in
    let module M = struct
      type formula = Formula.t
      let iter_trail f = Vec.iter (fun a -> f (Atom.lit self.store a)) t
      let[@inline] eval f = eval self (make_atom self f)
      let[@inline] eval_level f = eval_level self (make_atom self f)
    end in
    (module M)

  let mk_unsat (self:t) (us: unsat_cause) : _ Solver_intf.unsat_state =
    pp_all self 99 "UNSAT";
    let unsat_assumptions () = match us with
      | US_local {first=_; core} -> core
      | _ -> []
    in
    let unsat_conflict = match us with
      | US_false c -> fun() -> c
      | US_local {core=[]; _} -> assert false
      | US_local {first; core} ->
        let c = lazy (
          let core = List.rev core in (* increasing trail order *)
          assert (Atom.equal first @@ List.hd core);
          let proof_of (a:atom) = match Atom.reason self.store a with
            | Some Decision -> Clause.make_l self.store ~removable:true [a] Local
            | Some (Bcp c | Bcp_lazy (lazy c)) -> c
            | None -> assert false
          in
          let other_lits = List.filter (fun a -> not (Atom.equal a first)) core in
          let hist =
            Clause.make_l self.store ~removable:false [first] Local ::
            proof_of first ::
            List.map proof_of other_lits in
          Clause.make_l self.store ~removable:false [] (History hist)
        ) in
        fun () -> Lazy.force c
    in
    let get_proof () : Proof.t =
      let c = unsat_conflict () in
      Proof.prove self.store c
    in
    let module M = struct
      type nonrec atom = atom
      type clause = Clause.t
      type proof = Proof.t
      let get_proof = get_proof
      let unsat_conflict = unsat_conflict
      let unsat_assumptions = unsat_assumptions
    end in
    (module M)

  let add_clause_a self c lemma : unit =
    try
      let c = Clause.make_a self.store ~removable:false c (Hyp lemma) in
      add_clause_ self c
    with
    | E_unsat (US_false c) ->
      self.unsat_at_0 <- Some c

  let add_clause self c lemma : unit =
    try
      let c = Clause.make_l self.store ~removable:false c (Hyp lemma) in
      add_clause_ self c
    with
    | E_unsat (US_false c) ->
      self.unsat_at_0 <- Some c

  let solve ?(assumptions=[]) (st:t) : res =
    cancel_until st 0;
    Vec.clear st.assumptions;
    List.iter (Vec.push st.assumptions) assumptions;
    try
      solve_ st;
      Sat (mk_sat st)
    with E_unsat us ->
      Unsat (mk_unsat st us)

  let true_at_level0 st a =
    try
      let b, lev = eval_level st a in
      b && lev = 0
    with UndecidedLit -> false

  let[@inline] eval_atom self a : Solver_intf.lbool = eval_atom_ self a
end
[@@inline][@@specialise]


module Make_cdcl_t(Plugin : Solver_intf.PLUGIN_CDCL_T) =
  Make(struct
    include Plugin
    let has_theory = true
  end)
[@@inline][@@specialise]

module Make_pure_sat(Plugin : Solver_intf.PLUGIN_SAT) =
  Make(struct
  module Formula = Plugin.Formula
  type t = unit
  type proof = Plugin.proof
  let push_level () = ()
  let pop_levels _ _ = ()
  let partial_check () _ = ()
  let final_check () _ = ()
  let has_theory = false
end)
[@@inline][@@specialise]

