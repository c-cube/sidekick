
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
  module Map = Util.Int_map
end
type atom = Atom.t

module Clause : sig
  type t
  val size : t -> int
  val get : t -> int -> atom
  val iter : f:(atom -> unit) -> t -> unit
  val pp : t Fmt.printer
  val of_array : atom array -> t
end = struct
  type t = atom array
  let size = Array.length
  let get = Array.get
  let iter ~f c = Array.iter f c
  let pp out (self:t) = Fmt.Dump.array Atom.pp out self
  let of_array a = a
end
type clause = Clause.t

module Trace : sig
  type t

  val create : unit -> t

  val add_clause : t -> clause -> unit
  val add_input_clause : t -> clause -> unit
  val del_clause : t -> clause -> unit

  type event =
    | I of clause
    | A of clause
    | D of clause

  val iteri : t -> f:(int -> event -> unit) -> unit
  val events : t -> event Iter.t
  val size : t -> int
  val get : t -> int -> event

  val pp_event : event Fmt.printer

  val dump : out_channel -> t -> unit
end = struct
  type event =
    | I of clause
    | A of clause
    | D of clause

  type t = {
    evs: event Vec.t;
  }

  let create() : t =
    { evs=Vec.create() }

  let add_clause self c = Vec.push self.evs (A c)
  let add_input_clause self c = Vec.push self.evs (I c)
  let del_clause self c = Vec.push self.evs (D c)
  let get self i = Vec.get self.evs i
  let size self = Vec.size self.evs
  let events self = Vec.to_seq self.evs
  let iteri self ~f = Vec.iteri f self.evs

  let pp_event out = function
    | I c -> Fmt.fprintf out "(@[Input %a@])" Clause.pp c
    | A c -> Fmt.fprintf out "(@[Add %a@])" Clause.pp c
    | D c -> Fmt.fprintf out "(@[Del %a@])" Clause.pp c

  let dump oc self : unit =
    let fpf = Printf.fprintf in
    let pp_c out c = Clause.iter c ~f:(fun a -> fpf oc "%d " (Atom.to_int a)); in
    Vec.iter
      (function
        | I c -> fpf oc "i %a0\n" pp_c c;
        | A c -> fpf oc "%a0\n" pp_c c;
        | D c -> fpf oc "d %a0\n" pp_c c;
      )
      self.evs
end

(*
module Checker : sig
  type t

  val create : unit -> t

  val add_clause : t -> clause -> unit
  val remove_clause : t -> clause -> unit
end = struct
  type t = {
    clauses: unit Clause.Tbl.t;
  }
   *)

(** Forward checking.

    Each event is checked by reverse-unit propagation on previous events. *)
module Fwd_check : sig
  (** [check tr] checks the trace and returns [Ok ()] in case of
      success. In case of error it returns [Error idxs] where [idxs] are the
      indexes in the trace of the steps that failed. *)
  val check : Trace.t -> (unit, VecI32.t) result

end = struct
  module ISet = CCSet.Make(CCInt)

  type t = {
    assign: Bitvec.t; (* atom -> is_true(atom) *)
    trail: VecI32.t; (* current assignment *)
    mutable trail_ptr : int; (* offset in trail *)
    cs: clause Vec.t; (* index -> clause *)
    cs_recycle: int Vec.t; (* free elements in [cs] *)
    watches: ISet.t Vec.t; (* atom -> clauses it watches *)
    errors: VecI32.t;
  }

  let create() : t =
    { trail=VecI32.create();
      trail_ptr = 0;
      assign=Bitvec.create();
      cs=Vec.create();
      cs_recycle=Vec.create();
      watches=Vec.create();
      errors=VecI32.create();
    }

  let ensure_atom_ self (a:atom) =
    Bitvec.ensure_size self.assign (a:atom:>int);
    (* size: 2+atom, because: 1+atom makes atom valid, and if it's positive,
       2+atom is (¬atom)+1 *)
    Vec.ensure_size self.watches ISet.empty (2+(a:atom:>int));
    ()

  let[@inline] is_true self (a:atom) : bool =
    Bitvec.get self.assign (a:atom:>int)

  let[@inline] is_false self (a:atom) : bool =
    is_true self (Atom.neg a)

  let add_watch_ self (a:atom) cid =
    let set = Vec.get self.watches (a:atom:>int) in
    Vec.set self.watches (a:atom:>int) (ISet.add cid set)

  let remove_watch_ self (a:atom) cid =
    let set = Vec.get self.watches (a:atom:>int) in
    Vec.set self.watches (a:atom:>int) (ISet.remove cid set)

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

  (* TODO *)
  let propagate_in_clause_ (self:t) (cid:int) : unit =
    ()

  let propagate_atom_ self (a:atom) : unit =
    let set = Vec.get self.watches (a:atom:>int) in
    ISet.iter (propagate_in_clause_ self) set

  (* @raise Conflict if a clause is false *)
  let propagate_ (self:t) : unit =
    while self.trail_ptr < VecI32.size self.trail do
      let a = Atom.of_int_unsafe (VecI32.get self.trail self.trail_ptr) in
      self.trail_ptr <- 1 + self.trail_ptr;
      propagate_atom_ self a;
    done

  (* calls [f] and then restore trail to what it was *)
  let with_restore_trail_ self f =
    let trail_size0 = VecI32.size self.trail in
    let ptr = self.trail_ptr in

    let restore () =
      (* unassign new literals *)
      for i=trail_size0 to VecI32.size self.trail - 1 do
        let a = Atom.of_int_unsafe (VecI32.get self.trail i) in
        assert (is_true self a);
        Bitvec.set self.assign (a:atom:>int) false;
      done;

      (* remove literals from trail *)
      VecI32.shrink self.trail trail_size0;
      self.trail_ptr <- ptr
    in

    CCFun.finally ~h:restore ~f

  (* check event, return [true] if it's valid *)
  let check_ev (self:t) i (ev:Trace.event) : bool =
    Log.debugf 20 (fun k->k"(@[check-ev[%d]@ %a@])" i Trace.pp_event ev);

    (* add clause to the state *)
    let add_c_ (c:Clause.t) =
      Clause.iter c ~f:(ensure_atom_ self);

      (* allocate clause *)
      let cid =
        match Vec.pop_exn self.cs_recycle with
        | cid ->
          Vec.set self.cs cid c;
          cid
        | exception _ ->
          let cid = Vec.size self.cs in
          Vec.push self.cs c;
          cid
      in

      begin match Clause.size c with
        | 0 -> ()
        | 1 ->
          set_atom_true self (Clause.get c 0);
        | _ ->
          add_watch_ self (Atom.neg (Clause.get c 0)) cid;
          add_watch_ self (Atom.neg (Clause.get c 1)) cid;
      end;
      propagate_in_clause_ self cid; (* make sure watches are valid *)
      ()
    in

    match ev with
    | Trace.I c ->
      add_c_ c;
      true

    | Trace.A c ->

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
          propagate_ self;
          false
        with Conflict ->
          true
      in

      add_c_ c;
      ok

    | Trace.D _c ->
      true (* TODO*)

  let check trace : _ result =
    let self = create() in

    (* check each event in turn *)
    Trace.iteri trace
      ~f:(fun i ev ->
          let ok = check_ev self i ev in
          if not ok then (
            Log.debugf 10
              (fun k->k"(@[check.step.fail@ event[%d]@ :def %a@])" i Trace.pp_event ev);
            VecI32.push self.errors i
          ));

    (* TODO: check that the last event is empty clause *)

    Log.debugf 10 (fun k->k"found %d errors" (VecI32.size self.errors));
    if VecI32.is_empty self.errors
    then Ok ()
    else Error self.errors
end


(* TODO: backward checking + pruning of traces *)
