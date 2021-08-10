
module SDrup = Sidekick_drup

module Atom : sig
  include SDrup.ATOM with type t = private int

  val of_int : int -> t
end = struct
  type t = int
  type atom = t
  let hash = CCHash.int
  let equal : t -> t -> bool = (=)
  let compare : t -> t -> int = compare
  let[@inline] neg x = x lxor 1
  let[@inline] of_int x =
    let v = abs x lsl 1 in
    if x < 0 then neg v else v
  let[@inline] sign x = (x land 1) = 0
  let[@inline] to_int x = (if sign x then 1 else -1) * (x lsr 1)
  let pp out x =
    Fmt.fprintf out "%s%d" (if sign x then "+" else "-") (x lsr 1)
  let[@inline] of_int_unsafe i = i
  let dummy = 0
  module Assign = struct
    type t = Bitvec.t
    let create = Bitvec.create
    let ensure_size = Bitvec.ensure_size
    let is_true = Bitvec.get
    let[@inline] is_false self (a:atom) : bool =
      is_true self (neg a)
    let[@inline] is_unassigned self a =
      not (is_true self a) && not (is_false self a)
    let set = Bitvec.set
  end
  module Map = struct
    type 'a t = 'a Vec.t
    let create () = Vec.create ()
    let[@inline] ensure_has (self:_ t) a mk : unit =
      (* size: 2+atom, because: 1+atom makes atom valid, and if it's positive,
         2+atom is (¬atom)+1 *)
      Vec.ensure_size_with self mk (2+(a:atom:>int))
    let get = Vec.get
    let set = Vec.set
  end
  module Stack = struct
    include VecI32
    let create()=create()
  end
end

include SDrup.Make(Atom)

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
    let pp_c out c = Clause.iter c ~f:(fun a -> fpf oc "%d " (a:atom:>int)); in
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
    checker: Checker.t;
    errors: VecI32.t;
  }
  let create cstore : t = {
    checker=Checker.create cstore;
    errors=VecI32.create();
  }

  (* check event, return [true] if it's valid *)
  let check_op (self:t) i (op:Trace.op) : bool =
    Profile.with_ "check-op" @@ fun() ->
    Log.debugf 20 (fun k->k"(@[check-op :idx %d@ :op %a@])" i Trace.pp_op op);

    begin match op with
      | Trace.Input c ->
        Checker.add_clause self.checker c;
        true

      | Trace.Redundant c ->

        let ok = Checker.is_valid_drup self.checker c in
        Checker.add_clause self.checker c; (* now add clause *)
        ok

      | Trace.Delete c ->
        Checker.del_clause self.checker c;
        true

    end

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
            VecI32.push self.errors i
          ));

    Log.debugf 10 (fun k->k"found %d errors" (VecI32.size self.errors));
    if not !has_false then Error `No_empty_clause
    else if VecI32.size self.errors > 0 then Error (`Bad_steps self.errors)
    else Ok ()
end


