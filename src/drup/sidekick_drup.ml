
module Fmt = CCFormat
module VecI32 = VecI32

module Atom : sig
  type t = private int
  val of_int : int -> t
  val to_int : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val neg : t -> t
  val sign : t -> bool
  val pp : t Fmt.printer

  val dummy : t
  val of_int_unsafe : int -> t
  module Map : CCMap.S with type key = t
end = struct
  type t = int
  let hash = CCHash.int
  let equal : t -> t -> bool = (=)
  let compare : t -> t -> int = compare
  let neg x = x lxor 1
  let of_int x =
    let v = abs x lsl 1 in
    if x < 0 then neg v else v
  let sign x = (x land 1) = 0
  let to_int x = (if sign x then 1 else -1) * (x lsr 1)
  let pp out x =
    Fmt.fprintf out "%s%d" (if sign x then "+" else "-") (x lsr 1)
  let of_int_unsafe i = i
  let dummy = 0
  module Map = Util.Int_map
end
type atom = Atom.t

(** Boolean clauses *)
module Clause : sig
  type store
  val create : unit -> store
  type t
  val size : t -> int
  val get : t -> int -> atom
  val iter : f:(atom -> unit) -> t -> unit
  val watches: t -> atom * atom
  val set_watches : t -> atom * atom -> unit
  val pp : t Fmt.printer
  val of_list : store -> atom list -> t
  module Set : CCSet.S with type elt = t
  module Tbl : CCHashtbl.S with type key = t
end = struct
  module I_arr_tbl = CCHashtbl.Make(struct
      type t = atom array
      let equal = CCEqual.(array Atom.equal)
      let hash = CCHash.(array Atom.hash)
    end)
  type t = {
    id: int;
    atoms: atom array;
    mutable watches: atom * atom;
  }
  type store = {
    mutable n: int;
  }
  let create(): store =
    { n=0; }
  let[@inline] size self = Array.length self.atoms
  let[@inline] get self i = Array.get self.atoms i
  let[@inline] watches self = self.watches
  let[@inline] set_watches self w = self.watches <- w
  let[@inline] iter ~f self =
    for i=0 to Array.length self.atoms-1 do
      f (Array.unsafe_get self.atoms i)
    done
  let pp out (self:t) =
    let pp_watches out = function
      | (p,q) when p=Atom.dummy || q=Atom.dummy -> ()
      | (p,q) -> Fmt.fprintf out "@ :watches (%a,%a)" Atom.pp p Atom.pp q in
    Fmt.fprintf out "(@[cl[%d]@ %a%a])"
      self.id (Fmt.Dump.array Atom.pp) self.atoms pp_watches self.watches
  let of_list self atoms : t =
    (* normalize + find in table *)
    let atoms = List.sort_uniq Atom.compare atoms |> Array.of_list in
    let id = self.n in
    self.n <- 1 + self.n;
    let c = {atoms; id; watches=Atom.dummy, Atom.dummy} in
    c
  module As_key = struct
    type nonrec t=t
    let[@inline] hash a = CCHash.int a.id
    let[@inline] equal a b = a.id = b.id
    let[@inline] compare a b = compare a.id b.id
  end
  module Set = CCSet.Make(As_key)
  module Tbl = CCHashtbl.Make(As_key)
end
type clause = Clause.t

(** A DRUP trace, as a series of operations *)
module Trace : sig
  type t

  val create : Clause.store -> t
  val cstore : t -> Clause.store

  val add_clause : t -> clause -> unit
  val add_input_clause : t -> clause -> unit
  val del_clause : t -> clause -> unit

  (** Operator on the set of clauses *)
  type op =
    | Input of clause
    | Redundant of clause
    | Delete of clause

  val iteri : t -> f:(int -> op -> unit) -> unit
  val ops : t -> op Iter.t
  val size : t -> int
  val get : t -> int -> op

  val pp_op : op Fmt.printer

  val dump : out_channel -> t -> unit
end = struct
  type op =
    | Input of clause
    | Redundant of clause
    | Delete of clause

  type t = {
    cstore: Clause.store;
    ops: op Vec.t;
  }

  let create cstore : t =
    { cstore; ops=Vec.create() }

  let cstore self = self.cstore
  let add_clause self c = Vec.push self.ops (Redundant c)
  let add_input_clause self c = Vec.push self.ops (Input c)
  let del_clause self c = Vec.push self.ops (Delete c)
  let get self i = Vec.get self.ops i
  let size self = Vec.size self.ops
  let ops self = Vec.to_seq self.ops
  let iteri self ~f = Vec.iteri f self.ops

  let pp_op out = function
    | Input c -> Fmt.fprintf out "(@[Input %a@])" Clause.pp c
    | Redundant c -> Fmt.fprintf out "(@[Redundant %a@])" Clause.pp c
    | Delete c -> Fmt.fprintf out "(@[Delete %a@])" Clause.pp c

  let dump oc self : unit =
    let fpf = Printf.fprintf in
    let pp_c out c = Clause.iter c ~f:(fun a -> fpf oc "%d " (Atom.to_int a)); in
    Vec.iter
      (function
        | Input c -> fpf oc "i %a0\n" pp_c c;
        | Redundant c -> fpf oc "%a0\n" pp_c c;
        | Delete c -> fpf oc "d %a0\n" pp_c c;
      )
      self.ops
end

(** Forward checking.

    Each event is checked by reverse-unit propagation on previous events. *)
module Fwd_check : sig
  type error =
    [ `Bad_steps of VecI32.t
    | `No_empty_clause
    ]

  val pp_error : Trace.t -> error Fmt.printer

  (** [check tr] checks the trace and returns [Ok ()] in case of
      success. In case of error it returns [Error idxs] where [idxs] are the
      indexes in the trace of the steps that failed. *)
  val check : Trace.t -> (unit, error) result
end = struct
  module ISet = CCSet.Make(CCInt)

  type t = {
    cstore: Clause.store;
    assign: Bitvec.t; (* atom -> is_true(atom) *)
    trail: VecI32.t; (* current assignment *)
    mutable trail_ptr : int; (* offset in trail for propagation *)
    active_clauses: unit Clause.Tbl.t;
    watches: Clause.t Vec.t Vec.t; (* atom -> clauses it watches *)
    errors: VecI32.t;
  }

  let create cstore : t =
    { trail=VecI32.create();
      trail_ptr = 0;
      cstore;
      active_clauses=Clause.Tbl.create 32;
      assign=Bitvec.create();
      watches=Vec.create();
      errors=VecI32.create();
    }

  (* ensure data structures are big enough to handle [a] *)
  let ensure_atom_ self (a:atom) =
    Bitvec.ensure_size self.assign (a:atom:>int);
    (* size: 2+atom, because: 1+atom makes atom valid, and if it's positive,
       2+atom is (¬atom)+1 *)
    Vec.ensure_size_with self.watches Vec.create (2+(a:atom:>int));
    ()

  let[@inline] is_true self (a:atom) : bool =
    Bitvec.get self.assign (a:atom:>int)

  let[@inline] is_false self (a:atom) : bool =
    is_true self (Atom.neg a)

  let is_unassigned self a =
    not (is_true self a) && not (is_false self a)

  let add_watch_ self (a:atom) (c:clause) =
    Vec.push (Vec.get self.watches (a:atom:>int)) c

  let remove_watch_ self (a:atom) idx =
    let v = Vec.get self.watches (a:atom:>int) in
    Vec.fast_remove v idx

  exception Conflict

  let raise_conflict_ self a =
    Log.debugf 5 (fun k->k"conflict on atom %a" Atom.pp a);
    raise Conflict

  (* set atom to true *)
  let set_atom_true (self:t) (a:atom) : unit =
    if is_true self a then ()
    else if is_false self a then raise_conflict_ self a
    else (
      Bitvec.set self.assign (a:atom:>int) true;
      VecI32.push self.trail (a:atom:>int)
    )

  (* print the trail *)
  let pp_trail_ out self =
    let pp_a out i = Atom.pp out (Atom.of_int_unsafe i) in
    Fmt.fprintf out "(@[%a@])" (Fmt.iter pp_a) (VecI32.to_iter self.trail)

  exception Found_watch of atom
  exception Is_sat
  exception Is_undecided

  (* check if [c] is false in current trail *)
  let c_is_false_ self c =
    try Clause.iter c ~f:(fun a -> if not (is_false self a) then raise Exit); true
    with Exit -> false

  type propagation_res =
    | Keep
    | Remove

  (* do boolean propagation in [c], which is watched by the true literal [a] *)
  let propagate_in_clause_ (self:t) (a:atom) (c:clause) : propagation_res =
    assert (is_true self a);
    let a1, a2 = Clause.watches c in
    let na = Atom.neg a in
    (* [q] is the other literal in [c] such that [¬q] watches [c]. *)
    let q = if Atom.equal a1 na then a2 else (assert(a2==na); a1) in
    try
      if is_true self q then Keep (* clause is satisfied *)
      else (
        let n_unassigned = ref 0 in
        let unassigned_a = ref a in (* an unassigned atom, if [!n_unassigned > 0] *)
        if not (is_false self q) then unassigned_a := q;
        begin
          try
            Clause.iter c
              ~f:(fun ai ->
                  if is_true self ai then raise Is_sat (* no watch update *)
                  else if is_unassigned self ai then (
                    incr n_unassigned;
                    if q <> ai then unassigned_a := ai;
                    if !n_unassigned >= 2 then raise Is_undecided; (* early exit *)
                  );
                )
          with Is_undecided -> ()
        end;

        if !n_unassigned = 0 then (
          (* if we reach this point it means no literal is true, and none is
             unassigned. So they're all false and we have a conflict. *)
          assert (is_false self q);
          raise_conflict_ self a;
        ) else if !n_unassigned = 1 then (
          (* no lit is true, only one is unassigned: propagate it.
             no need to update the watches as the clause is satisfied. *)
          assert (is_unassigned self !unassigned_a);
          let p = !unassigned_a in
          Log.debugf 30 (fun k->k"(@[propagate@ :atom %a@ :reason %a@])" Atom.pp p Clause.pp c);
          set_atom_true self p;
          Keep
        ) else (
          (* at least 2 unassigned, just update the watch literal to [¬p] *)
          let p = !unassigned_a in
          assert (p <> q);
          Clause.set_watches c (q, p);
          add_watch_ self (Atom.neg p) c;
          Remove
        );
      )
    with
    | Is_sat -> Keep

  let propagate_atom_ self (a:atom) : unit =
    let v = Vec.get self.watches (a:atom:>int) in
    let i = ref 0 in
    while !i < Vec.size v do
      match propagate_in_clause_ self a (Vec.get v !i) with
      | Keep -> incr i;
      | Remove ->
        remove_watch_ self a !i
    done

  (* perform boolean propagation in a fixpoint
     @raise Conflict if a clause is false *)
  let bcp_fixpoint_ (self:t) : unit =
    Profile.with_ "bcp-fixpoint" @@ fun() ->
    while self.trail_ptr < VecI32.size self.trail do
      let a = Atom.of_int_unsafe (VecI32.get self.trail self.trail_ptr) in
      Log.debugf 50 (fun k->k"(@[bcp@ :atom %a@])" Atom.pp a);
      self.trail_ptr <- 1 + self.trail_ptr;
      propagate_atom_ self a;
    done

  (* calls [f] and then restore trail to what it was *)
  let with_restore_trail_ self f =
    let trail_size0 = VecI32.size self.trail in
    let ptr0 = self.trail_ptr in

    let restore () =
      (* unassign new literals *)
      for i=trail_size0 to VecI32.size self.trail - 1 do
        let a = Atom.of_int_unsafe (VecI32.get self.trail i) in
        assert (is_true self a);
        Bitvec.set self.assign (a:atom:>int) false;
      done;

      (* remove literals from trail *)
      VecI32.shrink self.trail trail_size0;
      self.trail_ptr <- ptr0
    in

    CCFun.finally ~h:restore ~f

  (* check event, return [true] if it's valid *)
  let check_op (self:t) i (op:Trace.op) : bool =
    Profile.with_ "check-op" @@ fun() ->
    Log.debugf 20 (fun k->k"(@[check-op :idx %d@ :op %a@])" i Trace.pp_op op);

    (* add clause to the state *)
    let add_c_ (c:Clause.t) =
      Log.debugf 50 (fun k->k"(@[add-clause@ %a@])" Clause.pp c);
      Clause.iter c ~f:(ensure_atom_ self);
      Clause.Tbl.add self.active_clauses c ();

      begin match Clause.size c with
        | 0 -> ()
        | 1 ->
          set_atom_true self (Clause.get c 0);
        | _ ->
          let c0 = Clause.get c 0 in
          let c1 = Clause.get c 1 in
          assert (c0 <> c1);
          Clause.set_watches c (c0,c1);
          (* make sure watches are valid *)
          if is_false self c0 then (
            match propagate_in_clause_ self (Atom.neg c0) c with
            | Keep -> add_watch_ self (Atom.neg c0) c;
            | Remove -> ()
          ) else (
            add_watch_ self (Atom.neg c0) c
          );
          if is_false self c1 then (
            match propagate_in_clause_ self (Atom.neg c1) c with
            | Keep -> add_watch_ self (Atom.neg c1) c;
            | Remove -> ()
          ) else (
            add_watch_ self (Atom.neg c1) c
          )
      end;
      ()
    in

    match op with
    | Trace.Input c ->
      add_c_ c;
      true

    | Trace.Redundant c ->

      (* negate [c], pushing each atom on trail, and see if we get [Conflict]
         by pure propagation *)
      let ok =
        try
          with_restore_trail_ self @@ fun () ->
          Clause.iter c
            ~f:(fun a ->
                if is_true self a then raise_notrace Conflict; (* tautology *)
                let a' = Atom.neg a in
                if is_true self a' then () else (
                  set_atom_true self a'
                ));
          bcp_fixpoint_ self;

          (*
          (* slow sanity check *)
          Clause.Tbl.iter
            (fun c () ->
               if c_is_false_ self c then
                Log.debugf 0 (fun k->k"clause is false: %a" Clause.pp c))
            self.active_clauses;
             *)

          false
        with Conflict ->
          true
      in

      (* now add clause *)
      add_c_ c;
      ok

    | Trace.Delete _c ->
      true (* TODO: actually remove the clause *)

  type error =
    [ `Bad_steps of VecI32.t
    | `No_empty_clause
    ]

  let pp_error trace out = function
    | `No_empty_clause -> Fmt.string out "no empty clause found"
    | `Bad_steps bad ->
      let n0 = VecI32.get bad 0 in
      Fmt.fprintf out
        "@[<v>checking failed on %d ops.@ @[<2>First failure is op[%d]:@ %a@]@]"
        (VecI32.size bad) n0
        Trace.pp_op (Trace.get trace n0)

  let check trace : _ result =
    let self = create (Trace.cstore trace) in

    (* check each event in turn *)
    let has_false = ref false in
    Trace.iteri trace
      ~f:(fun i op ->
          let ok = check_op self i op in
          if ok then (
            Log.debugf 50
              (fun k->k"(@[check.step.ok@ :idx %d@ :op %a@])" i Trace.pp_op op);

            (* check if op adds the empty clause *)
            begin match op with
              | (Trace.Redundant c | Trace.Input c) when Clause.size c = 0 ->
                has_false := true
              | _ -> ()
            end;
          ) else (
            Log.debugf 10
              (fun k->k"(@[check.step.fail@ :idx %d@ :op %a@])" i Trace.pp_op op);
            Log.debugf 50 (fun k->k"(@[trail: %a@])" pp_trail_ self);
            VecI32.push self.errors i
          ));

    Log.debugf 10 (fun k->k"found %d errors" (VecI32.size self.errors));
    if not !has_false then Error `No_empty_clause
    else if VecI32.size self.errors > 0 then Error (`Bad_steps self.errors)
    else Ok ()
end


(* TODO: backward checking + pruning of traces *)
