
module type PLUGIN = sig
  val has_theory : bool
  (** [true] iff the solver is parametrized by a theory, not just
      pure SAT. *)

  include Solver_intf.PLUGIN_CDCL_T
end

module type S = Solver_intf.S
module type PLUGIN_CDCL_T = Solver_intf.PLUGIN_CDCL_T
module Clause_pool_id = Solver_intf.Clause_pool_id

let invalid_argf fmt =
  Format.kasprintf (fun msg -> invalid_arg ("sidekick.sat: " ^ msg)) fmt

module Make(Plugin : PLUGIN)
= struct
  type lit = Plugin.lit
  type theory = Plugin.t
  type proof = Plugin.proof
  type proof_step = Plugin.proof_step
  type clause_pool_id = Clause_pool_id.t

  module Lit = Plugin.Lit
  module Proof = Plugin.Proof
  module Step_vec = Proof.Step_vec

  (* ### types ### *)

  (* a boolean variable (positive int) *)
  module Var0 : sig
    include Int_id.S
  end = struct
    include Int_id.Make()
  end
  type var = Var0.t

  (* a signed atom. +v is (v << 1), -v is (v<<1 | 1) *)
  module Atom0 : sig
    include Int_id.S
    val neg : t -> t
    val sign : t -> bool

    val of_var : var -> t
    val var : t -> var
    val abs : t -> t
    val pa : var -> t
    val na : var -> t
    module AVec : Vec_sig.S with type elt := t
    module ATbl : CCHashtbl.S with type key = t
  end = struct
    include Int_id.Make()
    let[@inline] neg i = (i lxor 1)
    let[@inline] sign i = (i land 1) = 0

    let[@inline] pa v = (v:var:>int) lsl 1
    let of_var = pa
    let[@inline] abs a = a land (lnot 1)
    let[@inline] var a = Var0.of_int_unsafe (a lsr 1)
    let[@inline] na v = (((v:var:>int) lsl 1) lor 1)
    module AVec = VecSmallInt
    module ATbl = CCHashtbl.Make(CCInt)
  end
  type atom = Atom0.t

  module Clause0 : sig
    include Int_id.S
    module Tbl : Hashtbl.S with type key = t
    module CVec : Vec_sig.S with type elt := t
  end = struct
    include Int_id.Make()
    module Tbl = Util.Int_tbl
    module CVec = VecSmallInt
  end
  type clause = Clause0.t

  and reason =
    | Decision
    | Bcp of clause
    | Bcp_lazy of clause lazy_t

  module AVec = Atom0.AVec
  (** Vector of atoms *)

  module ATbl = Atom0.ATbl
  (** Hashtbl of atoms *)

  module CVec = Clause0.CVec
  (** Vector of clauses *)

  (* ### stores ### *)

  module Lit_tbl = Hashtbl.Make(Lit)

  (* variable/atom store *)
  module Store = struct
    type cstore = {
      c_lits: atom array Vec.t; (* storage for clause content *)
      c_activity: Vec_float.t;
      c_recycle_idx: VecSmallInt.t; (* recycle clause numbers that were GC'd *)
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
      v_reason: reason option Vec.t; (* reason for assignment *)
      v_seen: Bitvec.t; (* generic temporary marker *)
      v_default_polarity: Bitvec.t; (* default polarity in decisions *)
      mutable v_count : int;

      (* atoms *)
      a_is_true: Bitvec.t;
      a_seen: Bitvec.t;
      a_form: lit Vec.t;
      (* TODO: store watches in clauses instead *)
      a_watched: Clause0.CVec.t Vec.t;
      a_proof_lvl0: proof_step ATbl.t; (* atom -> proof for it to be true at level 0 *)

      stat_n_atoms: int Stat.counter;

      (* clauses *)
      c_store: cstore;
    }
    type store = t

    let create ?(size=`Big) ~stat () : t =
      let size_map = match size with
        | `Tiny -> 8
        | `Small -> 16
        | `Big -> 4096
      in
      let stat_n_atoms = Stat.mk_int stat "sat.n-atoms" in
      { v_of_lit = Lit_tbl.create size_map;
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
        a_proof_lvl0=ATbl.create 16;
        stat_n_atoms;
        c_store={
          c_lits=Vec.create();
          c_activity=Vec_float.create();
          c_recycle_idx=VecSmallInt.create ~cap:0 ();
          c_proof=Step_vec.create ~cap:0 ();
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
      let lit = lit
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

      let proof_lvl0 self a = ATbl.get self.a_proof_lvl0 a
      let set_proof_lvl0 self a p = ATbl.replace self.a_proof_lvl0 a p

      let pp self fmt a = Lit.pp fmt (lit self a)

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
      let debug_reason _self out = function
        | n, _ when n < 0 -> Format.fprintf out "%%"
        | n, None -> Format.fprintf out "%d" n
        | n, Some Decision -> Format.fprintf out "@@%d" n
        | n, Some Bcp c ->
          Format.fprintf out "->%d/%d" n (c:>int)
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
          Lit.pp (lit self a)

      let debug_a self out vec =
        Array.iter (fun a -> Format.fprintf out "@[%a@]@ " (debug self) a) vec
      let debug_l self out l =
        List.iter (fun a -> Format.fprintf out "@[%a@]@ " (debug self) a) l
    end

    module Clause : sig
      include module type of Clause0 with type t = Clause0.t

      (** Make a clause with the given atoms *)

      val make_a : store -> removable:bool -> atom array -> proof_step -> t
      val make_l : store -> removable:bool -> atom list -> proof_step -> t
      val make_vec : store -> removable:bool -> atom Vec.t -> proof_step -> t

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

      val set_proof_step : store -> t -> proof_step -> unit
      val proof_step : store -> t -> proof_step

      val activity : store -> t -> float
      val set_activity : store -> t -> float -> unit

      val iter : store -> f:(atom -> unit) -> t -> unit
      val fold : store -> f:('a -> atom -> 'a) -> 'a -> t -> 'a
      val for_all : store -> f:(atom -> bool) -> t -> bool
      val exists : store -> f:(atom -> bool) -> t -> bool

      val atoms_a : store -> t -> atom array

      val lits_l : store -> t -> lit list
      val lits_a : store -> t -> lit array
      val lits_iter : store -> t -> lit Iter.t

      val short_name : store -> t -> string
      val pp : store -> Format.formatter -> t -> unit
      val debug : store -> Format.formatter -> t -> unit
    end = struct
      include Clause0

      (* TODO: store watch lists inside clauses *)

      let make_a (store:store) ~removable (atoms:atom array) proof_step : t =
        let {
          c_recycle_idx; c_lits; c_activity;
          c_attached; c_dead; c_removable; c_marked; c_proof;
        } = store.c_store in
        (* allocate new ID *)
        let cid =
          if VecSmallInt.is_empty c_recycle_idx then (
            Vec.size c_lits
          ) else VecSmallInt.pop c_recycle_idx
        in

        (* allocate space *)
        begin
          let new_len = cid + 1 in
          Vec.ensure_size c_lits [||] new_len;
          Vec_float.ensure_size c_activity new_len;
          Step_vec.ensure_size c_proof new_len;
          Bitvec.ensure_size c_attached new_len;
          Bitvec.ensure_size c_dead new_len;
          Bitvec.ensure_size c_removable new_len;
          Bitvec.ensure_size c_marked new_len;

          Bitvec.set c_removable cid removable;
        end;

        Vec.set c_lits cid atoms;
        Step_vec.set c_proof cid proof_step;

        let c = of_int_unsafe cid in
        c

      let make_l store ~removable atoms proof_rule : t =
        make_a store ~removable (Array.of_list atoms) proof_rule

      let make_vec store ~removable atoms proof_rule : t =
        make_a store ~removable (Vec.to_array atoms) proof_rule

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

      let[@inline] marked store c = Bitvec.get store.c_store.c_marked (c:t:>int)
      let[@inline] set_marked store c b = Bitvec.set store.c_store.c_marked (c:t:>int) b
      let[@inline] attached store c = Bitvec.get store.c_store.c_attached (c:t:>int)
      let[@inline] set_attached store c b = Bitvec.set store.c_store.c_attached (c:t:>int) b
      let[@inline] dead store c = Bitvec.get store.c_store.c_dead (c:t:>int)
      let[@inline] set_dead store c b = Bitvec.set store.c_store.c_dead (c:t:>int) b
      let[@inline] removable store c = Bitvec.get store.c_store.c_removable (c:t:>int)
      let[@inline] set_removable store c b = Bitvec.set store.c_store.c_removable (c:t:>int) b
      let[@inline] set_proof_step store c p = Step_vec.set store.c_store.c_proof (c:t:>int) p
      let[@inline] proof_step store c = Step_vec.get store.c_store.c_proof (c:t:>int)

      let dealloc store c : unit =
        assert (dead store c);
        let {c_lits; c_recycle_idx; c_activity; c_proof=_;
             c_dead; c_removable; c_attached; c_marked; } = store.c_store in

        (* clear data *)
        let cid = (c:t:>int) in
        Bitvec.set c_attached cid false;
        Bitvec.set c_dead cid false;
        Bitvec.set c_removable cid false;
        Bitvec.set c_marked cid false;
        Vec.set c_lits cid [||];
        Vec_float.set c_activity cid 0.;

        VecSmallInt.push c_recycle_idx cid; (* recycle idx *)
        ()

      let copy_flags store c1 c2 : unit =
        set_removable store c2 (removable store c1);
        ()

      let[@inline] activity store c = Vec_float.get store.c_store.c_activity (c:t:>int)
      let[@inline] set_activity store c f = Vec_float.set store.c_store.c_activity (c:t:>int) f

      let[@inline] make_removable store l proof_rule : t =
        make_l store ~removable:true l proof_rule

      let[@inline] make_removable_a store a proof_rule =
        make_a store ~removable:true a proof_rule

      let[@inline] make_permanent store l proof_rule : t =
        let c = make_l store ~removable:false l proof_rule in
        assert (not (removable store c)); (* permanent by default *)
        c

      let[@inline] atoms_a store c : atom array =
        Vec.get store.c_store.c_lits (c:t:>int)

      let lits_l store c : lit list =
        let arr = atoms_a store c in
        Util.array_to_list_map (Atom.lit store) arr

      let lits_a store c : lit array =
        let arr = atoms_a store c in
        Array.map (Atom.lit store) arr

      let lits_iter store c : lit Iter.t =
        let arr = atoms_a store c in
        Iter.of_array arr |> Iter.map (Atom.lit store)

      let short_name _store c = Printf.sprintf "cl[%d]" (c:t:>int)

      let pp store fmt c =
        Format.fprintf fmt "(cl[%d] : %a" (c:t:>int)
          (Atom.pp_a store) (atoms_a store c)

      let debug store out c =
        let atoms = atoms_a store c in
        Format.fprintf out
          "(@[cl[%d]@ {@[<hov>%a@]}@])"
          (c:t:>int)
          (Atom.debug_a store) atoms
    end

    (* allocate new variable *)
    let alloc_var_uncached_ ?default_pol:(pol=true) self (form:lit) : var =
      let {v_count; v_of_lit; v_level; v_heap_idx; v_weight;
           v_reason; v_seen; v_default_polarity; stat_n_atoms;
           a_is_true; a_seen; a_watched; a_form; c_store=_; a_proof_lvl0=_;
          } = self in

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

      assert (Vec.size a_form = 2 * (v:var:>int));
      Bitvec.ensure_size a_is_true (2*(v:var:>int));
      Bitvec.ensure_size a_seen (2*(v:var:>int));
      Vec.push a_form form;
      Vec.push a_watched (CVec.create ~cap:0 ());
      Vec.push a_form (Lit.neg form);
      Vec.push a_watched (CVec.create ~cap:0 ());
      assert (Vec.get a_form (Atom.of_var v:atom:>int) == form);

      v

    (* create new variable *)
    let alloc_var (self:t) ?default_pol (lit:lit) : var * Solver_intf.same_sign =
      let lit, same_sign = Lit.norm_sign lit in
      try Lit_tbl.find self.v_of_lit lit, same_sign
      with Not_found ->
        let v = alloc_var_uncached_ ?default_pol self lit in
        v, same_sign

    let clear_var (self:t) (v:var) : unit =
      Var.unmark self v;
      Atom.unmark self (Atom.pa v);
      Atom.unmark self (Atom.na v);
      ()

    let atom_of_var_ v same_sign : atom =
      if same_sign then Atom.pa v else Atom.na v

    let alloc_atom (self:t) ?default_pol lit : atom =
      let var, same_sign = alloc_var self ?default_pol lit in
      atom_of_var_ var same_sign

    let find_atom (self:t) lit : atom option =
      let lit, same_sign = Lit.norm_sign lit in
      match Lit_tbl.find self.v_of_lit lit with
      | v -> Some (atom_of_var_ v same_sign)
      | exception Not_found -> None
  end
  type store = Store.t

  module Atom = Store.Atom
  module Var = Store.Var
  module Clause = Store.Clause

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

  (** Passed to clause pools when it's time to garbage collect clauses *)
  module type GC_ARG = sig
    val store : Store.t
    val must_keep_clause : clause -> bool
    val flag_clause_for_gc : clause -> unit
  end

  (** A clause pool *)
  module type CLAUSE_POOL = sig
    val add : clause -> unit
    val descr : unit -> string
    val gc : (module GC_ARG) -> unit
    val iter : f:(clause -> unit) -> unit
    val needs_gc : unit -> bool
    val size : unit -> int
  end

  (* a clause pool *)
  type clause_pool = (module CLAUSE_POOL)

  (* a pool with garbage collection determined by [P] *)
  module Make_gc_cp(P:sig
      val descr : unit -> string
      val max_size : int ref
    end)() : CLAUSE_POOL = struct
    let clauses_ : clause Vec.t = Vec.create()
    (* Use a [Vec] so we can sort it.
       TODO: when we can sort any vec, come back to that. *)

    let descr = P.descr
    let add c = Vec.push clauses_ c
    let iter ~f = Vec.iter f clauses_
    let push_level () = ()
    let pop_levels _ = ()
    let size () = Vec.size clauses_
    let needs_gc () = size () > !P.max_size

    let gc (module G:GC_ARG) : unit =
      (* find clauses to GC *)
      let to_be_pushed_back = CVec.create() in

      (* sort by decreasing activity *)
      Vec.sort clauses_
        (fun c1 c2 ->
           compare (Clause.activity G.store c2) (Clause.activity G.store c1));

      while Vec.size clauses_ > !P.max_size do
        let c = Vec.pop_exn clauses_ in
        if G.must_keep_clause c then (
          CVec.push to_be_pushed_back c; (* must keep it, it's on the trail *)
        ) else (
          G.flag_clause_for_gc c;
        )
      done;
      (* transfer back clauses we had to keep *)
      CVec.iter ~f:(Vec.push clauses_) to_be_pushed_back;
      ()
  end

  let make_gc_clause_pool_ ~descr ~max_size () : clause_pool =
    (module Make_gc_cp(struct
         let descr=descr
         let max_size=max_size
       end)())

  let[@inline] cp_descr_ (module P:CLAUSE_POOL) : string = P.descr()
  let[@inline] cp_size_ (module P:CLAUSE_POOL) : int = P.size()
  let[@inline] cp_needs_gc_ (module P:CLAUSE_POOL) : bool = P.needs_gc()
  let[@inline] cp_add_ (module P:CLAUSE_POOL) c : unit = P.add c
  let[@inline] cp_to_iter_ (module P:CLAUSE_POOL) yield : unit = P.iter ~f:yield

  (* initial limit for the number of learnt clauses, 1/3 of initial
      number of clauses by default *)
  let learntsize_factor = 1. /. 3.

  (* Singleton type containing the current state *)
  type t = {
    store : store;
    (* atom/var/clause store *)

    th: theory;
    (* user defined theory *)

    proof: Proof.t; (* the proof object *)

    (* Clauses are simplified for efficiency purposes. In the following
       vectors, the comments actually refer to the original non-simplified
       clause. *)

    clauses_hyps : CVec.t;
    (* clauses added by the user, never removed *)

    max_clauses_learnt : int ref;
    (* used to direct GC in {!clauses_learnt} *)

    clauses_learnt : clause_pool;
    (* learnt clauses (tautologies true at any time, whatever the user level).
       GC'd regularly. *)

    clauses_to_add_learnt : CVec.t;
    (* Clauses either assumed or pushed by the theory, waiting to be added. *)

    clauses_to_add_in_pool : (clause * clause_pool) Vec.t;
    (* clauses to add into a pool *)

    clauses_dead : CVec.t;
    (* dead clauses, to be removed at next GC.
       invariant: all satisfy [Clause.dead store c]. *)

    clause_pools : clause_pool Vec.t;
    (* custom clause pools *)

    mutable unsat_at_0: clause option;
    (* conflict at level 0, if any *)

    mutable next_decisions : atom list;
    (* When the last conflict was a semantic one (mcsat),
       this stores the next decision to make;
       if some theory wants atoms to be decided on (for theory combination),
       store them here. *)

    trail : AVec.t;
    (* decision stack + propagated elements (atoms or assignments). *)

    var_levels : VecSmallInt.t;
    (* decision levels in [trail]  *)

    mutable assumptions: AVec.t;
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

    temp_atom_vec : AVec.t;
    temp_clause_vec : CVec.t;
    temp_step_vec : Step_vec.t;

    mutable var_incr : float;
    (* increment for variables' activity *)

    mutable clause_incr : float;
    (* increment for clauses' activity *)

    mutable on_conflict : (t -> Clause.t -> unit) option;
    mutable on_decision : (t -> lit -> unit) option;
    mutable on_learnt : (t -> Clause.t -> unit) option;
    mutable on_gc : (t -> lit array -> unit) option;

    stat: Stat.t;
    n_conflicts: int Stat.counter;
    n_propagations : int Stat.counter;
    n_decisions : int Stat.counter;
    n_restarts : int Stat.counter;
    n_minimized_away : int Stat.counter;
  }

  type solver = t

  (* intial restart limit *)
  let restart_first = 100

  let _nop_on_conflict (_:atom array) = ()

  (* Starting environment. *)
  let create_ ~store ~proof ~stat ~max_clauses_learnt (th:theory) : t = {
    store; th;
    unsat_at_0=None;
    next_decisions = [];

    max_clauses_learnt;
    clauses_hyps = CVec.create();
    clauses_learnt =
      make_gc_clause_pool_
        ~descr:(fun () -> "cp.learnt-clauses")
        ~max_size:max_clauses_learnt ();
    clauses_to_add_learnt = CVec.create ();
    clauses_to_add_in_pool = Vec.create();
    clauses_dead = CVec.create();

    clause_pools = Vec.create();

    to_clear=Vec.create();
    temp_clause_vec=CVec.create();
    temp_atom_vec=AVec.create();
    temp_step_vec=Step_vec.create();

    th_head = 0;
    elt_head = 0;

    trail = AVec.create ();
    var_levels = VecSmallInt.create();
    assumptions= AVec.create();

    order = H.create store;

    var_incr = 1.;
    clause_incr = 1.;

    proof;

    stat;
    n_conflicts = Stat.mk_int stat "sat.n-conflicts";
    n_decisions = Stat.mk_int stat "sat.n-decisions";
    n_propagations = Stat.mk_int stat "sat.n-propagations";
    n_restarts = Stat.mk_int stat "sat.n-restarts";
    n_minimized_away = Stat.mk_int stat "sat.n-confl-lits-minimized-away";

    on_conflict = None;
    on_decision= None;
    on_learnt = None;
    on_gc = None;
  }

  let create
      ?on_conflict ?on_decision ?on_learnt ?on_gc ?(stat=Stat.global)
      ?(size=`Big) ~proof
      (th:theory) : t =
    let store = Store.create ~size ~stat () in
    let max_clauses_learnt = ref 0 in
    let self = create_ ~max_clauses_learnt ~store ~proof ~stat th in
    self.on_decision <- on_decision;
    self.on_conflict <- on_conflict;
    self.on_learnt <- on_learnt;
    self.on_gc <- on_gc;
    self

  (* iterate on all learnt clauses, pools included *)
  let iter_clauses_learnt_ (self:t) ~f : unit =
    let[@inline] iter_pool (module P:CLAUSE_POOL) = P.iter ~f in
    iter_pool self.clauses_learnt;
    Vec.iter iter_pool self.clause_pools;
    ()

  let[@inline] decision_level st = VecSmallInt.size st.var_levels
  let[@inline] nb_clauses st = CVec.size st.clauses_hyps
  let stat self = self.stat
  let clause_pool_descr self (p:clause_pool_id) =
    let pool = Vec.get self.clause_pools (p:>int) in
    cp_descr_ pool


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

  (* find atom for the lit, if any *)
  let[@inline] find_atom_ (self:t) (p:lit) : atom option =
    Store.find_atom self.store p

  (* create a new atom, pushing it into the decision queue if needed *)
  let make_atom_ (self:t) ?default_pol (p:lit) : atom =
    let a = Store.alloc_atom self.store ?default_pol p in
    if Atom.level self.store a < 0 then (
      insert_var_order self (Atom.var a);
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
      let update_clause c =
        Clause.set_activity store c (Clause.activity store c *. 1e-20)
      in
      iter_clauses_learnt_ self ~f:update_clause;
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

  (* get/build the proof for [a], which must be an atom true at level 0.
     This uses a global cache to avoid repeated computations, as many clauses
     might resolve against a given 0-level atom. *)
  let rec proof_of_atom_lvl0_ (self:t) (a:atom) : proof_step =
    assert (Atom.is_true self.store a && Atom.level self.store a = 0);

    begin match Atom.proof_lvl0 self.store a with
      | Some p -> p
      | None ->

        let p =
          match Atom.reason self.store a with
          | None -> assert false
          | Some Decision -> assert false (* no decisions at level0 *)
          | Some (Bcp c2 | Bcp_lazy (lazy c2)) ->
            Log.debugf 50
              (fun k->k"(@[sat.proof-of-atom-lvl0.clause@ %a@])"
                  (Clause.debug self.store) c2);

            let steps = ref [] in
            (* recurse, so we get the whole level-0 resolution graph *)
            Clause.iter self.store c2
              ~f:(fun a2 ->
                  if not (Var.equal (Atom.var a) (Atom.var a2)) then (
                    Log.debugf 50
                      (fun k->k"(@[sat.proof-of-atom-lvl0@ :of %a@ \
                                @[:resolve-with@ %a@]@])"
                          (Atom.debug self.store) a (Atom.debug self.store) a2);

                    let p2 = proof_of_atom_lvl0_ self (Atom.neg a2) in
                    steps := p2 :: !steps;
                  ));

            let proof_c2 = Clause.proof_step self.store c2 in
            if !steps = [] then proof_c2
            else (
              Proof.emit_redundant_clause
                (Iter.return (Atom.lit self.store a))
                ~hyps:Iter.(cons proof_c2 (of_list !steps))
                self.proof
            )
        in

        Atom.set_proof_lvl0 self.store a p; (* put in cache *)
        p
    end

  (* Preprocess clause, by doing the following:

     - Partition literals for new clauses, into:
       - true literals (maybe makes the clause trivial if the lit is proved true at level 0)
       - unassigned literals, yet to be decided
       - false literals (not suitable to watch, those at level 0 can be removed from the clause)
       and order them as such in the result.

     - Also, removes literals that are false at level0, and returns a proof for
       their removal.
     - Also, removes duplicates.
  *)
  let preprocess_clause_ (self:t) (c:Clause.t) : Clause.t =
    let store = self.store in
    let res0_proofs = ref [] in (* steps of resolution at level 0 *)
    let add_proof_ p = res0_proofs := p :: !res0_proofs in

    let trues = Vec.create () in
    let unassigned = Vec.create() in
    let falses = Vec.create() in

    (* cleanup marks used to detect duplicates *)
    let cleanup () =
      Clause.iter store c
        ~f:(fun a -> Store.clear_var store (Atom.var a));
    in

    let consider_atom (a:atom) : unit =
      if not (Atom.marked store a) then (
        Atom.mark store a;
        if Atom.marked_both store a then (
          raise Trivial
        );

        if Atom.is_true store a then (
          let lvl = Atom.level store a in
          if lvl = 0 then (
            (* Atom true at level 0 gives a trivially true clause *)
            raise Trivial
          );
          Vec.push trues a;

        ) else if Atom.is_false store a then (
          let lvl = Atom.level store a in
          if lvl = 0 then (
            (* Atom var false at level 0 can be eliminated from the clause,
               but we need to kepp in mind that we used another clause to simplify it. *)
            Log.debugf 50
              (fun k->k"(@[sat.preprocess-clause.resolve-away-lvl0@ %a@])"
                  (Atom.debug store) a);

            let p = proof_of_atom_lvl0_ self (Atom.neg a) in
            add_proof_ p;
          ) else (
            Vec.push falses a;
          )

        ) else (
          Vec.push unassigned a
        );
      )
    in

    begin
      try
        Clause.iter store c ~f:consider_atom;
        cleanup()
      with e ->
        cleanup();
        raise e
    end;

    (* merge all atoms together *)
    let atoms =
      let v = trues in
      Vec.append ~into:v unassigned;
      Vec.append ~into:v falses;
      Vec.to_array v
    in

    if !res0_proofs = [] then (
      (* no change except in the order of literals *)
      Clause.make_a store atoms
        ~removable:(Clause.removable store c)
        (Clause.proof_step store c)

    ) else (
      assert (Array.length atoms < Clause.n_atoms store c);
      (* some atoms were removed by resolution with level-0 clauses *)
      Log.debugf 30 (fun k->k"(@[sat.add-clause.resolved-lvl-0@ :into [@[%a@]]@])"
                        (Atom.debug_a store) atoms);
      let proof =
        let lits =
          Clause.atoms_a store c
          |> Iter.of_array
          |> Iter.map (Atom.lit store)
        in
        Proof.emit_redundant_clause lits
          ~hyps:Iter.(cons (Clause.proof_step self.store c) (of_list !res0_proofs))
          self.proof
      in
      Clause.make_a
        store atoms proof
        ~removable:(Clause.removable store c)
    )

  let new_decision_level st =
    assert (st.th_head = AVec.size st.trail);
    assert (st.elt_head = AVec.size st.trail);
    VecSmallInt.push st.var_levels (AVec.size st.trail);
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
    CVec.push (Atom.watched store (Atom.neg (Clause.atoms_a store c).(0))) c;
    CVec.push (Atom.watched store (Atom.neg (Clause.atoms_a store c).(1))) c;
    Clause.set_attached store c true;
    ()

  (* Backtracking.
     Used to backtrack, i.e cancel down to [lvl] excluded,
     i.e we want to go back to the state the solver was in
         after decision level [lvl] was created and fully propagated. *)
  let cancel_until (self:t) lvl =
    let store = self.store in
    assert (lvl >= 0);
    (* Nothing to do if we try to backtrack to a non-existent level. *)
    if decision_level self <= lvl then (
      Log.debugf 20 (fun k -> k "(@[sat.cancel-until.nop@ :already-at-level <= %d@])" lvl)
    ) else (
      Log.debugf 5 (fun k -> k "(@[sat.cancel-until %d@])" lvl);
      (* We set the head of the solver and theory queue to what it was. *)
      let head = ref (VecSmallInt.get self.var_levels lvl) in
      self.elt_head <- !head;
      self.th_head <- !head;
      (* Now we need to cleanup the vars that are not valid anymore
         (i.e to the right of elt_head in the queue. *)
      for c = self.elt_head to AVec.size self.trail - 1 do
        let a = AVec.get self.trail c in
        (* Atom literal is unassigned, we nedd to add it back to
           the heap of potentially assignable literals, unless it has
           a level lower than [lvl], in which case we just move it back. *)
        (* Atom variable is not true/false anymore, one of two things can happen: *)
        if Atom.level store a <= lvl then (
          (* It is a late propagation, which has a level
             lower than where we backtrack, so we just move it to the head
             of the queue, to be propagated again. *)
          AVec.set self.trail !head a;
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
      AVec.shrink self.trail !head;
      VecSmallInt.shrink self.var_levels lvl;
      Plugin.pop_levels self.th n;
      (* TODO: for scoped clause pools, backtrack them *)
      self.next_decisions <- [];
    );
    ()

  let pp_unsat_cause self out = function
    | US_local {first=_; core} ->
      Format.fprintf out "(@[unsat-cause@ :false-assumptions %a@])"
        (Format.pp_print_list (Atom.pp self.store)) core
    | US_false c ->
      Format.fprintf out "(@[unsat-cause@ :false %a@])" (Clause.debug self.store) c

  let prove_unsat self (us:clause) : clause =
    if Proof.enabled self.proof && Clause.n_atoms self.store us > 0 then (
      (* reduce [c] to an empty clause, all its literals should be false at level 0 *)
      Log.debugf 1 (fun k -> k "(@[sat.prove-unsat@ :from %a@])" (Clause.debug self.store) us);

      (* accumulate proofs of all level-0 lits *)
      let pvec = self.temp_step_vec in
      assert (Step_vec.is_empty pvec);
      Clause.iter self.store us
        ~f:(fun a ->
            assert (Atom.is_false self.store a && Atom.level self.store a=0);
            begin match Atom.reason self.store a with
              | Some (Bcp c | Bcp_lazy (lazy c)) ->
                let p = Clause.proof_step self.store c in
                Step_vec.push pvec p
              | _ -> assert false
            end);

      let p_empty =
        Proof.emit_redundant_clause Iter.empty ~hyps:(Step_vec.to_iter pvec) self.proof
      in
      Step_vec.clear pvec;
      let c_empty = Clause.make_l self.store [] ~removable:false p_empty in

      c_empty
    ) else us

  (* Unsatisfiability is signaled through an exception, since it can happen
     in multiple places (adding new clauses, or solving for instance). *)
  let report_unsat self (us:unsat_cause) : _ =
    Log.debugf 3 (fun k -> k "(@[sat.unsat-conflict@ %a@])" (pp_unsat_cause self) us);
    let us = match us with
      | US_false c ->
        self.unsat_at_0 <- Some c;
        (match self.on_learnt with Some f -> f self c | None -> ());
        let p = Clause.proof_step self.store c in
        Proof.emit_unsat p self.proof;
        US_false c
      | US_local _ -> us
    in
    raise (E_unsat us)

  (* Boolean propagation.
     Wrapper function for adding a new propagated lit. *)
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
    Atom.set_is_true store a true;
    Var.set_level store (Atom.var a) lvl;
    Var.set_reason store (Atom.var a) (Some reason);
    AVec.push self.trail a;
    Log.debugf 20
      (fun k->k "(@[sat.enqueue[%d]@ %a@])"
          (AVec.size self.trail) (Atom.debug store) a);
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


   (* abtraction of the assignment level of [v] in an integer *)
   let[@inline] abstract_level_ (self:t) (v:var) : int =
     1 lsl (Var.level self.store v land 31)

   exception Non_redundant

   (* can we remove [a] by self-subsuming resolutions with other lits
      of the learnt clause? *)
   let lit_redundant (self:t) (abstract_levels:int) (steps:Step_vec.t) (v:var) : bool =
     let store = self.store in
     let to_unmark = self.to_clear in
     let steps_size_init = Step_vec.size steps in

     (* save current state of [to_unmark] *)
     let top = Vec.size to_unmark in
     let rec aux v =
       match Var.reason store v with
       | None -> assert false
       | Some Decision -> raise_notrace Non_redundant
       | Some (Bcp c | Bcp_lazy (lazy c)) ->
         let c_atoms = Clause.atoms_a store c in
         assert (Var.equal v (Atom.var c_atoms.(0)));
         if Proof.enabled self.proof then (
           Step_vec.push steps (Clause.proof_step self.store c);
         );

         (* check that all the other lits of [c] are marked or redundant *)
         for i = 1 to Array.length c_atoms - 1 do
           let v2 = Atom.var c_atoms.(i) in
           if not (Var.marked store v2) && Var.level store v2 > 0 then (
             match Var.reason store v2 with
             | None -> assert false
             | Some (Bcp _ | Bcp_lazy _)
               when (abstract_level_ self v2 land abstract_levels) <> 0 ->
               (* possibly removable, its level may comprise an atom in learnt clause *)
               Vec.push to_unmark v2;
               Var.mark store v2;
               aux v2
             | Some _ ->
               raise_notrace Non_redundant
           )
         done
     in
     try aux v; true
     with Non_redundant ->
       (* clear new marks, they are not actually redundant *)
       for i = top to Vec.size to_unmark-1 do
         Var.unmark store (Vec.get to_unmark i)
       done;
       Vec.shrink to_unmark top;
       Step_vec.shrink steps steps_size_init; (* restore proof *)
       false

   (* minimize conflict by removing atoms whose propagation history
      is ultimately self-subsuming with [lits] *)
   let minimize_conflict (self:t) (_c_level:int)
       (learnt: AVec.t) (steps: Step_vec.t) : unit =
     let store = self.store in

     (* abstraction of the levels involved in the conflict at all,
        as logical "or" of each literal's approximate level *)
     let abstract_levels =
       AVec.fold_left (fun lvl a -> lvl lor abstract_level_ self (Atom.var a)) 0 learnt
     in

     let j = ref 1 in
     for i=1 to AVec.size learnt - 1 do
       let a = AVec.get learnt i in
       let keep =
         begin match Atom.reason store a with
           | Some Decision -> true (* always keep decisions *)
           | Some (Bcp _ | Bcp_lazy _) ->
             not (lit_redundant self abstract_levels steps (Atom.var a))
           | None -> assert false
         end
       in
       if keep then (
         AVec.set learnt !j a;
         incr j
       ) else (
         Stat.incr self.n_minimized_away;
       )
     done;
     AVec.shrink learnt !j;
     ()

  (* result of conflict analysis, containing the learnt clause and some
     additional info. *)
  type conflict_res = {
    cr_backtrack_lvl : int; (* level to backtrack to *)
    cr_learnt: atom array; (* lemma learnt from conflict *)
    cr_is_uip: bool; (* conflict is UIP? *)
    cr_steps: Step_vec.t;
  }

  (* conflict analysis, starting with top of trail and conflict clause *)
  let analyze (self:t) c_clause : conflict_res =
    let store = self.store in

    let to_unmark = self.to_clear in (* for cleanup *)
    Vec.clear to_unmark;
    let learnt = self.temp_atom_vec in
    AVec.clear learnt;

    let steps = self.temp_step_vec in (* for proof *)
    assert (Step_vec.is_empty steps);

    (* loop variables *)
    let pathC  = ref 0 in
    let continue = ref true in
    let blevel = ref 0 in
    let c = ref (Some c_clause) in (* current clause to analyze/resolve *)
    let tr_ind = ref (AVec.size self.trail - 1) in (* pointer in trail *)

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
          if Proof.enabled self.proof then (
            Step_vec.push steps (Clause.proof_step self.store clause);
          );

          (* visit the current predecessors *)
          let atoms = Clause.atoms_a store clause in
          for j = 0 to Array.length atoms - 1 do
            let q = atoms.(j) in
            assert (Atom.has_value store q);
            assert (Atom.level store q >= 0);
            if Atom.level store q = 0 then (
              assert (Atom.is_false store q);
              if Proof.enabled self.proof then (
                let step = proof_of_atom_lvl0_ self (Atom.neg q) in
                Step_vec.push steps step;
              )
            );
            if not (Var.marked store (Atom.var q)) then (
              Var.mark store (Atom.var q);
              Vec.push to_unmark (Atom.var q);
              if Atom.level store q > 0 then (
                var_bump_activity self (Atom.var q);
                if Atom.level store q >= conflict_level then (
                  incr pathC;
                ) else (
                  AVec.push learnt q;
                  blevel := max !blevel (Atom.level store q)
                )
              )
            )
          done
      end;

      (* look for the next node to expand *)
      while
        let a = AVec.get self.trail !tr_ind in
        Log.debugf 30
          (fun k -> k "(@[sat.analyze-conflict.at-trail-elt@ %a@])" (Atom.debug store) a);
        (not (Var.marked store (Atom.var a))) ||
        (Atom.level store a < conflict_level)
      do
        decr tr_ind;
      done;
      let p = AVec.get self.trail !tr_ind in
      decr pathC;
      decr tr_ind;
      match !pathC, Atom.reason store p with
      | 0, _ ->
        continue := false;
        AVec.push learnt (Atom.neg p)
      | n, Some (Bcp cl | Bcp_lazy (lazy cl)) ->
        assert (n > 0);
        assert (Atom.level store p >= conflict_level);
        c := Some cl
      | _, (None | Some Decision) -> assert false
    done;

    Log.debugf 10
      (fun k->k "(@[sat.conflict.res@ %a@])" (AVec.pp @@ Atom.debug store) learnt);

    (* minimize conflict, to get a more general lemma *)
    minimize_conflict self conflict_level learnt steps;

    let cr_steps = Step_vec.copy steps in
    Step_vec.clear self.temp_step_vec;

    (* cleanup marks *)
    Vec.iter (Store.clear_var store) to_unmark;
    Vec.clear to_unmark;

    (* put high-level literals first, so that:
       - they make adequate watch lits
       - the first literal is the UIP, if any *)
    let cr_learnt = AVec.to_array learnt in
    AVec.clear learnt;
    Array.sort (fun p q -> compare (Atom.level store q) (Atom.level store p)) cr_learnt;

    (* put_high_level_atoms_first a; *)
    let level, is_uip = backtrack_lvl self cr_learnt in
    Log.debugf 10
      (fun k->k "(@[sat.conflict.res.final@ :lvl %d@ {@[%a@]}@])"
          level (Util.pp_array @@ Atom.debug store) cr_learnt);

    { cr_backtrack_lvl = level;
      cr_learnt;
      cr_is_uip = is_uip;
      cr_steps;
    }

  (* Get the correct vector to insert a clause in. *)
  let[@inline] add_clause_to_vec_ ~pool self c =
    if Clause.removable self.store c && Clause.n_atoms self.store c > 2 then (
      (* add clause to some pool/set of clauses *)
      cp_add_ pool c
    ) else (
      CVec.push self.clauses_hyps c
    )

  (* add the learnt clause to the clause database, propagate, etc. *)
  let record_learnt_clause (self:t) ~pool (confl:clause) (cr:conflict_res): unit =
    let store = self.store in
    begin match cr.cr_learnt with
      | [| |] -> assert false
      | [|fuip|] ->
        assert (cr.cr_backtrack_lvl = 0 && decision_level self = 0);
        if Atom.is_false store fuip then (
          (* incompatible at level 0 *)
          report_unsat self (US_false confl)
        ) else (
          let p =
            Proof.emit_redundant_clause
              (Iter.of_array cr.cr_learnt |> Iter.map (Atom.lit self.store))
              ~hyps:(Step_vec.to_iter cr.cr_steps)
              self.proof
          in
          let uclause = Clause.make_a store ~removable:true cr.cr_learnt p in

          (match self.on_learnt with Some f -> f self uclause | None -> ());
          (* no need to attach [uclause], it is true at level 0 *)
          enqueue_bool self fuip ~level:0 (Bcp uclause)
        )

      | _ ->
        let fuip = cr.cr_learnt.(0) in
        let p =
          Proof.emit_redundant_clause
            (Iter.of_array cr.cr_learnt |> Iter.map (Atom.lit self.store))
            ~hyps:(Step_vec.to_iter cr.cr_steps) self.proof
        in
        let lclause = Clause.make_a store ~removable:true cr.cr_learnt p in

        add_clause_to_vec_ ~pool self lclause;
        attach_clause self lclause;
        clause_bump_activity self lclause;
        (match self.on_learnt with Some f -> f self lclause | None -> ());
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
    record_learnt_clause ~pool:self.clauses_learnt self confl cr

  (* Add a new clause, simplifying, propagating, and backtracking if
     the clause is false in the current trail *)
  let add_clause_ (self:t) ~pool (init:clause) : unit =
    let store = self.store in
    Log.debugf 30 (fun k -> k "(@[sat.add-clause@ @[<hov>%a@]@])" (Clause.debug store) init);
    (* Insertion of new lits is done before simplification. Indeed, else a lit in a
       trivial clause could end up being not decided on, which is a bug. *)
    Clause.iter store init ~f:(fun x -> insert_var_order self (Atom.var x));
    try
      (* preprocess to remove dups, sort literals, etc. *)
      let clause = preprocess_clause_ self init in
      assert (Clause.removable store clause = Clause.removable store init);

      Log.debugf 5 (fun k->k "(@[sat.new-clause@ @[<hov>%a@]@])" (Clause.debug store) clause);
      let atoms = Clause.atoms_a self.store clause in
      match atoms with
      | [||] ->
        report_unsat self @@ US_false clause
      | [|a|]   ->
        cancel_until self 0;
        if Atom.is_false store a then (
          (* cannot recover from this *)
          report_unsat self @@ US_false clause
        ) else if Atom.is_true store a then (
          () (* atom is already true, (at level 0) nothing to do *)
        ) else (
          Log.debugf 40
            (fun k->k "(@[sat.add-clause.unit-clause@ :propagating %a@])" (Atom.debug store) a);
          add_clause_to_vec_ ~pool self clause;
          enqueue_bool self a ~level:0 (Bcp clause)
        )
      | _ ->
        let a = atoms.(0) in
        let b = atoms.(1) in
        add_clause_to_vec_ ~pool self clause;
        if Atom.is_false store a then (
          (* Atom need to be sorted in decreasing order of decision level,
             or we might watch the wrong literals. *)
          put_high_level_atoms_first store (Clause.atoms_a store clause);
          attach_clause self clause;
          add_boolean_conflict self clause
        ) else (
          attach_clause self clause;
          if Atom.is_false store b &&
             not (Atom.has_value store a) then (
            (* unit, propagate [a] *)
            let lvl = Array.fold_left (fun m a -> max m (Atom.level store a)) 0 atoms in
            cancel_until self lvl;
            Log.debugf 50 (fun k->k"(@[sat.add-clause.propagate@ %a@ :lvl %d@])"
                              (Atom.debug store) a lvl);
            enqueue_bool self a ~level:lvl (Bcp clause)
          )
        )
    with Trivial ->
      Log.debugf 5
        (fun k->k "(@[sat.add-clause@ :ignore-trivial @[%a@]@])" (Clause.debug store) init)

  let[@inline never] flush_clauses_ (self:t) : unit =
    while not @@ CVec.is_empty self.clauses_to_add_learnt do
      let c = CVec.pop self.clauses_to_add_learnt in
      add_clause_ ~pool:self.clauses_learnt self c
    done;
    while not @@ Vec.is_empty self.clauses_to_add_in_pool do
      let c, pool = Vec.pop_exn self.clauses_to_add_in_pool in
      add_clause_ ~pool self c
    done;
    ()

  let[@inline] has_no_new_clauses (self:t) : bool =
    CVec.is_empty self.clauses_to_add_learnt && Vec.is_empty self.clauses_to_add_in_pool

  let[@inline] flush_clauses self =
    if not (has_no_new_clauses self) then (
      flush_clauses_ self
    )

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
            CVec.push (Atom.watched store (Atom.neg ak)) c;
            assert (Clause.equal (CVec.get (Atom.watched store a) i) c);
            CVec.fast_remove (Atom.watched store a) i;
            raise_notrace Exit
          )
        done;
        (* no watch lit found *)
        if Atom.is_false store first then (
          (* clause is false *)
          self.elt_head <- AVec.size self.trail;
          raise_notrace (Conflict c)
        ) else (
          Stat.incr self.n_propagations;
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
      if i >= CVec.size watched then ()
      else (
        let c = CVec.get watched i in
        assert (Clause.attached store c);
        let j =
          if Clause.dead store c then (
            i (* remove on the fly *)
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

  let[@inline] slice_get st i = AVec.get st.trail i

  let acts_add_clause self ?(keep=false) (l:lit list) (p:proof_step): unit =
    let atoms = List.rev_map (make_atom_ self) l in
    let removable = not keep in
    let c = Clause.make_l self.store ~removable atoms p in
    Log.debugf 5 (fun k->k "(@[sat.th.add-clause@ %a@])" (Clause.debug self.store) c);
    CVec.push self.clauses_to_add_learnt c

  let acts_add_clause_in_pool self ~pool (l:lit list) (p:proof_step): unit =
    let atoms = List.rev_map (make_atom_ self) l in
    let removable = true in
    let c = Clause.make_l self.store ~removable atoms p in
    let pool = Vec.get self.clause_pools (pool:clause_pool_id:>int) in
    Log.debugf 5 (fun k->k "(@[sat.th.add-clause-in-pool@ %a@ :pool %s@])"
                     (Clause.debug self.store) c
                     (cp_descr_ pool));
    Vec.push self.clauses_to_add_in_pool (c, pool)

  let acts_add_decision_lit (self:t) (f:lit) (sign:bool) : unit =
    let store = self.store in
    let a = make_atom_ self f in
    let a = if sign then a else Atom.neg a in
    if not (Atom.has_value store a) then (
      Log.debugf 10 (fun k->k "(@[sat.th.add-decision-lit@ %a@])" (Atom.debug store) a);
      self.next_decisions <- a :: self.next_decisions
    )

  let acts_raise self (l:lit list) (p:proof_step) : 'a =
    let atoms = List.rev_map (make_atom_ self) l in
    (* conflicts can be removed *)
    let c = Clause.make_l self.store ~removable:true atoms p in
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

  let acts_propagate (self:t) f (expl:(_,proof_step) Solver_intf.reason) =
    let store = self.store in
    match expl with
    | Solver_intf.Consequence mk_expl ->
      let p = make_atom_ self f in
      if Atom.is_true store p then ()
      else if Atom.is_false store p then (
        let lits, proof = mk_expl() in
        let l = List.rev_map (fun f -> Atom.neg @@ make_atom_ self f) lits in
        check_consequence_lits_false_ self l;
        let c = Clause.make_l store ~removable:true (p :: l) proof in
        raise_notrace (Th_conflict c)
      ) else (
        insert_var_order self (Atom.var p);
        let c = lazy (
          let lits, proof = mk_expl () in
          let l = List.rev_map (fun f -> Atom.neg @@ make_atom_ self f) lits in
          (* note: we can check that invariant here in the [lazy] block,
             as conflict analysis will run in an environment where
             the literals should be true anyway, since it's an extension of the
             current trail
             (otherwise the propagated lit would have been backtracked and
             discarded already.) *)
          check_consequence_lits_false_ self l;
          Clause.make_l store ~removable:true (p :: l) proof
        ) in
        let level = decision_level self in
        Stat.incr self.n_propagations;
        enqueue_bool self p ~level (Bcp_lazy c)
      )

  let[@specialise] acts_iter self ~full head f : unit =
    for i = (if full then 0 else head) to AVec.size self.trail-1 do
      let a = AVec.get self.trail i in
      f (Atom.lit self.store a);
    done

  let eval_atom_ self a =
    if Atom.is_true self.store a then Solver_intf.L_true
    else if Atom.is_false self.store a then Solver_intf.L_false
    else Solver_intf.L_undefined

  let[@inline] acts_eval_lit self (f:lit) : Solver_intf.lbool =
    let a = make_atom_ self f in
    eval_atom_ self a

  let[@inline] acts_add_lit self ?default_pol f : unit =
    ignore (make_atom_ ?default_pol self f : atom)

  let[@inline] current_slice st : _ Solver_intf.acts =
    let module M = struct
      type nonrec proof = proof
      type nonrec proof_step = proof_step
      type nonrec clause_pool_id = clause_pool_id
      type nonrec lit = lit
      let proof = st.proof
      let iter_assumptions=acts_iter st ~full:false st.th_head
      let eval_lit= acts_eval_lit st
      let add_lit=acts_add_lit st
      let add_clause = acts_add_clause st
      let add_clause_in_pool = acts_add_clause_in_pool st
      let propagate = acts_propagate st
      let raise_conflict c pr=acts_raise st c pr
      let add_decision_lit=acts_add_decision_lit st
    end in
    (module M)

  (* full slice, for [if_sat] final check *)
  let[@inline] full_slice st : _ Solver_intf.acts =
    let module M = struct
      type nonrec proof = proof
      type nonrec proof_step = proof_step
      type nonrec clause_pool_id = clause_pool_id
      type nonrec lit = lit
      let proof = st.proof
      let iter_assumptions=acts_iter st ~full:true st.th_head
      let eval_lit= acts_eval_lit st
      let add_lit=acts_add_lit st
      let add_clause = acts_add_clause st
      let add_clause_in_pool = acts_add_clause_in_pool st
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
    assert (self.elt_head = AVec.size self.trail);
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
    assert (st.elt_head <= AVec.size st.trail);
    if st.elt_head = AVec.size st.trail then (
      theory_propagate st
    ) else (
      match
        while st.elt_head < AVec.size st.trail do
          let a = AVec.get st.trail st.elt_head in
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
    let idx = ref (AVec.size self.trail - 1) in
    Var.mark store (Atom.var a);
    let seen = ref [Atom.var a] in
    while !idx >= 0 do
      let a' = AVec.get self.trail !idx in
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

  (* GC: remove some learnt clauses.
     This works even during the proof with a non empty trail. *)
  let reduce_clause_db (self:t) : unit =
    let store = self.store in

    Log.debugf 3 (fun k->k "(@[sat.gc-clauses.start :max-learnt %d@])"
                     !(self.max_clauses_learnt));

    let to_be_gc = self.temp_clause_vec in (* clauses to collect *)
    assert (CVec.is_empty to_be_gc);

    (* atoms whose watches will need to be rebuilt to filter out
       dead clauses *)
    let dirty_atoms = self.temp_atom_vec in
    assert (AVec.is_empty dirty_atoms);

    (* [a] is watching at least one removed clause, we'll need to
       trim its watchlist *)
    let[@inline] mark_dirty_atom a =
      if not (Atom.marked store a) then (
        Atom.mark store a;
        AVec.push dirty_atoms a;
      )
    in

    (* iter on the clauses that are used to explain atoms on the trail,
       which we must therefore keep for now as they might participate in
       conflict resolution *)
    let iter_clauses_on_trail ~f : unit =
      AVec.iter self.trail
        ~f:(fun a ->
           match Atom.reason store a with
           | Some (Bcp c) -> f c
           | Some (Bcp_lazy lc) when Lazy.is_val lc -> f (Lazy.force lc)
           | _ -> ());
    in

    iter_clauses_on_trail ~f:(fun c -> Clause.set_marked store c true);

    (* first, mark clauses used on the trail, we cannot GC them.
       TODO: once we use DRUP, we can avoid marking level-0 explanations
       as they will never participate in resolution. *)
    AVec.iter
      ~f:(fun a ->
         match Atom.reason store a with
         | Some (Bcp c) -> Clause.set_marked store c true
         | Some (Bcp_lazy lc) when Lazy.is_val lc ->
           Clause.set_marked store (Lazy.force lc) true
         | _ -> ())
      self.trail;

    (* GC the clause [c] *)
    let flag_clause_for_gc c : unit =
      assert (Clause.removable store c);
      Log.debugf 10 (fun k->k"(@[sat.gc.will-collect@ %a@])" (Clause.debug store) c);
      CVec.push to_be_gc c;
      Clause.set_dead store c true;
      let atoms = Clause.atoms_a store c in
      mark_dirty_atom (Atom.neg atoms.(0)); (* need to remove from watchlists *)
      mark_dirty_atom (Atom.neg atoms.(1));
      (match self.on_gc with
       | Some f -> let lits = Clause.lits_a store c in f self lits
       | None -> ());
      Proof.del_clause
        (Clause.proof_step store c) (Clause.lits_iter store c) self.proof;
    in

    let gc_arg =
      (module struct
        let store = self.store
        let flag_clause_for_gc = flag_clause_for_gc
        let must_keep_clause c = Clause.marked store c
      end : GC_ARG)
    in

    (* GC a pool, if it needs it *)
    let gc_pool (module P:CLAUSE_POOL) : unit =
      if P.needs_gc () then (
        Log.debugf 5 (fun k->k"(@[sat.gc.pool@ :descr %s@])" (P.descr()));
        P.gc gc_arg
      )
    in

    gc_pool self.clauses_learnt;
    Vec.iter gc_pool self.clause_pools;

    let n_collected = CVec.size to_be_gc in

    (* update watchlist of dirty atoms *)
    AVec.iter dirty_atoms
      ~f:(fun a ->
         assert (Atom.marked store a);
         Atom.unmark store a;
         let w = Atom.watched store a in
         CVec.filter_in_place (fun c -> not (Clause.dead store c)) w);
    AVec.clear dirty_atoms;

    (* actually remove the clauses now that they are detached *)
    CVec.iter ~f:(Clause.dealloc store) to_be_gc;
    CVec.clear to_be_gc;

    (* remove marks on clauses on the trail *)
    iter_clauses_on_trail ~f:(fun c -> Clause.set_marked store c false);

    Log.debugf 3 (fun k->k "(@[sat.gc.done :collected %d@])" n_collected);
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
      Stat.incr self.n_decisions;
      (match self.on_decision with Some f -> f self (Atom.lit self.store atom) | None -> ());
    )

  and pick_branch_lit self : unit =
    match self.next_decisions with
    | atom :: tl ->
      self.next_decisions <- tl;
      pick_branch_aux self atom
    | [] when decision_level self < AVec.size self.assumptions ->
      (* use an assumption *)
      let a = AVec.get self.assumptions (decision_level self) in
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
  let search (st:t) ~(max_conflicts:int) : unit =
    Log.debugf 3
      (fun k->k "(@[sat.search@ :max-conflicts %d@ :max-learnt %d@])"
          max_conflicts !(st.max_clauses_learnt));
    let n_conflicts = ref 0 in
    while true do
      match propagate st with
      | Some confl -> (* Conflict *)
        incr n_conflicts;
        (* When the theory has raised Unsat, add_boolean_conflict
           might 'forget' the initial conflict clause, and only add the
           analyzed backtrack clause. So in those case, we use add_clause
           to make sure the initial conflict clause is also added. *)
        if Clause.attached st.store confl then (
          add_boolean_conflict st confl
        ) else (
          add_clause_ ~pool:st.clauses_learnt st confl
        );
        Stat.incr st.n_conflicts;
        (match st.on_conflict with Some f -> f st confl | None -> ());

      | None -> (* No Conflict *)
        assert (st.elt_head = AVec.size st.trail);
        assert (st.elt_head = st.th_head);
        if max_conflicts > 0 && !n_conflicts >= max_conflicts then (
          Log.debug 1 "(sat.restarting)";
          cancel_until st 0;
          Stat.incr st.n_restarts;
          raise_notrace Restart
        );
        (* if decision_level() = 0 then simplify (); *)

        let do_gc =
          (!(st.max_clauses_learnt) > 0 &&
           cp_size_ st.clauses_learnt  -
           AVec.size st.trail > !(st.max_clauses_learnt))
          || Vec.exists cp_needs_gc_ st.clause_pools
        in
        if do_gc then (
          reduce_clause_db st;
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
    Log.debugf 5 (fun k->k "(@[sat.solve :assms %d@])" (AVec.size self.assumptions));
    check_unsat_ self;
    try
      flush_clauses self; (* add initial clauses *)
      let max_conflicts = ref (float_of_int restart_first) in
      let max_learnt = ref ((float_of_int (nb_clauses self)) *. learntsize_factor) in
      while true do
        begin try
            self.max_clauses_learnt := int_of_float !max_learnt ;
            search self ~max_conflicts:(int_of_float !max_conflicts)
          with
          | Restart ->
            max_conflicts := !max_conflicts *. restart_inc;
            max_learnt    := !max_learnt *. learntsize_inc
          | E_sat ->
            assert (self.elt_head = AVec.size self.trail &&
                    has_no_new_clauses self &&
                    self.next_decisions=[]);
            begin match Plugin.final_check self.th (full_slice self) with
              | () ->
                if self.elt_head = AVec.size self.trail &&
                   has_no_new_clauses self &&
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
                Stat.incr self.n_conflicts;
                (match self.on_conflict with Some f -> f self c | None -> ());
                CVec.push self.clauses_to_add_learnt c;
                flush_clauses self;
            end;
        end
      done
    with E_sat -> ()

  let assume self cnf : unit =
    List.iter
      (fun l ->
         let atoms = Util.array_of_list_map (make_atom_ self) l in
         let proof = Proof.emit_input_clause (Iter.of_list l) self.proof in
         let c = Clause.make_a self.store ~removable:false atoms proof in
         Log.debugf 10 (fun k -> k "(@[sat.assume-clause@ @[<hov 2>%a@]@])"
                           (Clause.debug self.store) c);
         CVec.push self.clauses_to_add_learnt c)
      cnf

  let[@inline] theory st = st.th
  let[@inline] store st = st.store
  let[@inline] proof st = st.proof

  let[@inline] add_lit self ?default_pol lit =
    ignore (make_atom_ self lit ?default_pol : atom)
  let[@inline] set_default_pol (self:t) (lit:lit) (pol:bool) : unit =
    let a = make_atom_ self lit ~default_pol:pol in
    Var.set_default_pol self.store (Atom.var a) pol

  (* Result type *)
  type res =
    | Sat of Lit.t Solver_intf.sat_state
    | Unsat of (lit,clause,proof_step) Solver_intf.unsat_state

  let pp_all self lvl status =
    Log.debugf lvl
      (fun k -> k
          "(@[<v>sat.full-state :res %s - Full summary:@,@[<hov 2>Trail:@\n%a@]@,\
           @[<hov 2>Hyps:@\n%a@]@,@[<hov 2>Lemmas:@\n%a@]@,@]@."
          status
          (AVec.pp @@ Atom.debug self.store) self.trail
          (CVec.pp @@ Clause.debug self.store) self.clauses_hyps
          (Util.pp_iter @@ Clause.debug self.store)
          (cp_to_iter_ self.clauses_learnt))

  let mk_sat (self:t) : Lit.t Solver_intf.sat_state =
    pp_all self 99 "SAT";
    let t = self.trail in
    let module M = struct
      type lit = Lit.t
      let iter_trail f = AVec.iter ~f:(fun a -> f (Atom.lit self.store a)) t
      let[@inline] eval f = eval self (make_atom_ self f)
      let[@inline] eval_level f = eval_level self (make_atom_ self f)
    end in
    (module M)

  (* make a clause that contains no level-0 false literals, by resolving
     against them. This clause can be used in a refutation proof.
     Note that the clause might still contain some {b assumptions}. *)
  let resolve_with_lvl0 (self:t) (c:clause) : clause =
    let lvl0 = ref [] in
    let res = ref [] in
    let to_unmark = self.temp_atom_vec in
    assert (AVec.is_empty to_unmark);

    (* resolve against the root cause of [a] being false *)
    let resolve_with_a (a:atom) : unit =
      assert (Atom.is_false self.store a && Atom.level self.store a=0);
      if not (Var.marked self.store (Atom.var a)) then (
        Log.debugf 50 (fun k->k"(@[sat.resolve-lvl0@ :atom %a@])" (Atom.debug self.store) a);
        AVec.push to_unmark a;
        Var.mark self.store (Atom.var a);

        let p = proof_of_atom_lvl0_ self (Atom.neg a) in
        lvl0 := p :: !lvl0;
      )
    in

    Clause.iter self.store c
      ~f:(fun a ->
          if Atom.level self.store a = 0 then resolve_with_a a
        );
    AVec.iter to_unmark ~f:(fun a -> Var.unmark self.store (Atom.var a));
    AVec.clear to_unmark;

    if !lvl0 = [] then (
      c (* no resolution happened *)
    ) else (
      let proof =
        let lits = Iter.of_list !res |> Iter.map (Atom.lit self.store) in
        let hyps = Iter.of_list (Clause.proof_step self.store c :: !lvl0) in
        Proof.emit_redundant_clause lits ~hyps self.proof
      in
      Clause.make_l self.store ~removable:false !res proof
    )

  let mk_unsat (self:t) (us: unsat_cause) : _ Solver_intf.unsat_state =
    pp_all self 99 "UNSAT";
    let store = store self in
    let unsat_assumptions () = match us with
      | US_local {first=_; core} ->
        let lits = Iter.of_list core |> Iter.map (Atom.lit store) in
        lits
      | _ -> Iter.empty
    in
    let unsat_conflict = match us with
      | US_false c0 ->
        Log.debugf 10 (fun k->k"(@[sat.unsat-conflict-clause@ %a@])" (Clause.debug store) c0);
        let c = resolve_with_lvl0 self c0 in
        Log.debugf 10 (fun k->k"(@[sat.unsat-conflict-clause.proper@ %a@])" (Clause.debug store) c);
        (fun() -> c)
      | US_local {core=[]; _} -> assert false
      | US_local {first; core} ->
        (* TODO: do we need to filter out literals? *)
        let c = lazy (
          let core = List.rev core in (* increasing trail order *)
          assert (Atom.equal first @@ List.hd core);
          let proof =
            let lits = Iter.of_list core |> Iter.map (Atom.lit self.store) in
            Proof.emit_unsat_core lits self.proof in
          Clause.make_l self.store ~removable:false [] proof
        ) in
        fun () -> Lazy.force c
    in
    let module M = struct
      type nonrec lit = lit
      type nonrec proof = proof_step
      type clause = Clause.t
      let unsat_conflict = unsat_conflict
      let unsat_assumptions = unsat_assumptions
      let unsat_proof () =
        let c = unsat_conflict() in
        Clause.proof_step self.store c
    end in
    (module M)

  let add_clause_atoms_ self ~pool ~removable (c:atom array) (pr:proof_step) : unit =
    try
      let c = Clause.make_a self.store ~removable c pr in
      add_clause_ ~pool self c
    with
    | E_unsat (US_false c) ->
      self.unsat_at_0 <- Some c

  let add_clause_a self c pr : unit =
    let c = Array.map (make_atom_ self) c in
    add_clause_atoms_ ~pool:self.clauses_learnt ~removable:false self c pr

  let add_clause self (c:lit list) (pr:proof_step) : unit =
    let c = Util.array_of_list_map (make_atom_ self) c in
    add_clause_atoms_ ~pool:self.clauses_learnt ~removable:false self c pr

  let add_clause_a_in_pool self ~pool c (pr:proof_step) : unit =
    let c = Array.map (make_atom_ self) c in
    let pool = Vec.get self.clause_pools (pool:clause_pool_id:>int) in
    add_clause_atoms_ ~pool ~removable:true self c pr

  let add_clause_in_pool self ~pool (c:lit list) dp : unit =
    let c = Util.array_of_list_map (make_atom_ self) c in
    let pool = Vec.get self.clause_pools (pool:clause_pool_id:>int) in
    add_clause_atoms_ ~pool ~removable:true self c dp

  let add_input_clause self (c:lit list) =
    let pr = Proof.emit_input_clause (Iter.of_list c) self.proof in
    add_clause self c pr

  let add_input_clause_a self c =
    let pr = Proof.emit_input_clause (Iter.of_array c) self.proof in
    add_clause_a self c pr

  let new_clause_pool_gc_fixed_size ~descr ~size (self:t) : clause_pool_id =
    let p =
      make_gc_clause_pool_
        ~descr:(fun () -> descr)
        ~max_size:(ref size)
        () in
    let id = Vec.size self.clause_pools in
    Vec.push self.clause_pools p;
    Clause_pool_id._unsafe_of_int id

  let solve ?(assumptions=[]) (self:t) : res =
    cancel_until self 0;
    AVec.clear self.assumptions;
    List.iter
      (fun lit ->
         let a = make_atom_ self lit in
         AVec.push self.assumptions a)
      assumptions;
    try
      solve_ self;
      Sat (mk_sat self)
    with E_unsat us ->
      (* FIXME
      (* emit empty clause *)
      Proof.with_proof self.proof (Proof.emit_redundant_clause Iter.empty);
         *)
      Unsat (mk_unsat self us)

  let true_at_level0 (self:t) (lit:lit) : bool =
    match find_atom_ self lit with
    | None -> false
    | Some a ->
      try
        let b, lev = eval_level self a in
        b && lev = 0
      with UndecidedLit -> false

  let[@inline] eval_lit self (lit:lit) : Solver_intf.lbool =
    match find_atom_ self lit with
    | Some a -> eval_atom_ self a
    | None -> Solver_intf.L_undefined
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
    type lit = Plugin.lit
    type proof = Plugin.proof
    type proof_step = Plugin.proof_step
    module Lit = Plugin.Lit
    module Proof = Plugin.Proof
    type t = unit
    let push_level () = ()
    let pop_levels _ _ = ()
    let partial_check () _ = ()
    let final_check () _ = ()
    let has_theory = false
  end)
[@@inline][@@specialise]

