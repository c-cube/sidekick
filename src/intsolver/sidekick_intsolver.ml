
module type ARG = sig
  module Z : Sidekick_arith.INT

  type term
  type lit

  val pp_term : term Fmt.printer
  val pp_lit : lit Fmt.printer

  module T_map : CCMap.S with type key = term
end

module type S = sig
  module A : ARG

  module Op : sig
    type t =
      | Leq
      | Lt
      | Eq
    val pp : t Fmt.printer
  end

  type t

  val create : unit -> t

  val push_level : t -> unit

  val pop_levels : t -> int -> unit

  val assert_ :
    t ->
    (A.Z.t * A.term) list -> Op.t -> A.Z.t ->
    lit:A.lit ->
    unit

  val define :
    t ->
    A.term ->
    (A.Z.t * A.term) list ->
    unit

  module Cert : sig
    type t
    val pp : t Fmt.printer

    val lits : t -> A.lit Iter.t
  end

  module Model : sig
    type t
    val pp : t Fmt.printer

    val eval : t -> A.term -> A.Z.t option
  end

  type result =
    | Sat of Model.t
    | Unsat of Cert.t

  val pp_result : result Fmt.printer

  val check : t -> result

  (**/**)
  val _check_invariants : t -> unit
  (**/**)
end



module Make(A : ARG)
  : S with module A = A
= struct
  module BVec = Backtrack_stack
  module A = A
  open A

  module Op = struct
    type t =
      | Leq
      | Lt
      | Eq

    let pp out = function
      | Leq -> Fmt.string out "<="
      | Lt -> Fmt.string out "<"
      | Eq -> Fmt.string out "="
  end

  module Linexp = struct
    type t = Z.t T_map.t
    let is_empty = T_map.is_empty
    let empty : t = T_map.empty

    let pp out (self:t) : unit =
      let pp_pair out (t,z) =
        if Z.(z = one) then A.pp_term out t
        else Fmt.fprintf out "%a · %a" Z.pp z A.pp_term t in
      if is_empty self then Fmt.string out "0"
      else Fmt.fprintf out "(@[%a@])"
          Fmt.(iter ~sep:(return "@ + ") pp_pair) (T_map.to_iter self)

    let iter = T_map.iter
    let return t : t = T_map.add t Z.one empty
    let neg self : t = T_map.map Z.neg self
    let mult n self =
      if Z.(n = zero) then empty
      else T_map.map (fun c -> Z.(c * n)) self

    let add (self:t) (c:Z.t) (t:term) : t =
      let n = Z.(c + T_map.get_or ~default:Z.zero t self) in
      if Z.(n = zero)
      then T_map.remove t self
      else T_map.add t n self

    let merge (self:t) (other:t) : t =
      T_map.fold
        (fun t c m -> add m c t)
        other self

    let of_list l : t =
      List.fold_left (fun self (c,t) -> add self c t) empty l

    (* map each term to a linexp *)
    let flat_map f (self:t) : t =
      T_map.fold
        (fun t c m ->
           let t_le = mult c (f t) in
           merge m t_le
        )
        empty self
  end

  module Cert = struct
    type t = unit
    let pp = Fmt.unit

    let lits _ = Iter.empty (* TODO *)
  end

  module Model = struct
    type t = {
      m: Z.t T_map.t;
    } [@@unboxed]

    let pp out self =
      let pp_pair out (t,z) = Fmt.fprintf out "(@[%a := %a@])" A.pp_term t Z.pp z in
      Fmt.fprintf out "(@[model@ %a@])"
        Fmt.(iter ~sep:(return "@ ") pp_pair) (T_map.to_iter self.m)

    let empty : t = {m=T_map.empty}

    let eval (self:t) t : Z.t option = T_map.get t self.m
  end

  module Constr = struct
    type t = {
      le: Linexp.t;
      const: Z.t;
      op: Op.t;
      lits: lit Bag.t;
    }

    let pp out self =
      Fmt.fprintf out "(@[%a@ %a %a@])" Linexp.pp self.le Op.pp self.op Z.pp self.const
  end

  type t = {
    defs: (term * Linexp.t) BVec.t;
    cs: Constr.t BVec.t;
  }

  let create() : t =
    { defs=BVec.create();
      cs=BVec.create(); }

  let push_level self =
    BVec.push_level self.defs;
    BVec.push_level self.cs;
    ()

  let pop_levels self n =
    BVec.pop_levels self.defs n ~f:(fun _ -> ());
    BVec.pop_levels self.cs n ~f:(fun _ -> ());
    ()

  type result =
    | Sat of Model.t
    | Unsat of Cert.t

  let pp_result out = function
    | Sat m -> Fmt.fprintf out "(@[SAT@ %a@])" Model.pp m
    | Unsat cert -> Fmt.fprintf out "(@[UNSAT@ %a@])" Cert.pp cert

  let assert_ (self:t) l op c ~lit : unit =
    let le = Linexp.of_list l in
    let c = {Constr.le; const=c; op; lits=Bag.return lit} in
    Log.debugf 10 (fun k->k "(@[sidekick.intsolver.assert@ %a@])" Constr.pp c);
    BVec.push self.cs c

  (* TODO: check before hand that [t] occurs nowhere else *)
  let define (self:t) t l : unit =
    let le = Linexp.of_list l in
    BVec.push self.defs (t,le)

  (* #### checking #### *)

  module Check_ = struct
    module LE = Linexp

    type op =
      | Leq
      | Lt
      | Eq
      | Eq_mod of {
          prime: Z.t;
          pow: int;
        } (* modulo prime^pow *)

    type constr = {
      le: LE.t;
      const: Z.t;
      op: op;
      lits: lit Bag.t;
    }

    type state = {
      mutable rw: LE.t T_map.t; (* rewrite rules *)
      mutable vars: int T_map.t; (* variables in at least one constraint *)
      mutable constrs: constr list;
    }
    (* main solving state. mutable, but copied for backtracking.
       invariant: variables in [rw] do not occur anywhere else
    *)

    (* perform rewriting on the linear expression *)
    let norm_le (self:state) (le:LE.t) : LE.t =
      LE.flat_map
        (fun t -> try T_map.find t self.rw with Not_found -> LE.return t)
        le

    let[@inline] count_v self t : int = T_map.get_or ~default:0 t self.vars
    let[@inline] incr_v (self:state) (t:term) : unit =
      self.vars <- T_map.add t (1 + count_v self t) self.vars
    let decr_v (self:state) (t:term) : unit =
      let n = count_v self t - 1 in
      assert (n >= 0);
      self.vars <-
        (if n=0 then T_map.remove t self.vars
         else T_map.add t n self.vars)

    let add_constr (self:state) (c:constr) =
      let c = {c with le=norm_le self c.le } in
      LE.iter (fun t _ -> incr_v self t) c.le;
      self.constrs <- c :: self.constrs

    let remove_constr (self:state) (c:constr) =
      LE.iter (fun t _ -> decr_v self t) c.le

    let create (self:t) : state =
      let state = {
        vars=T_map.empty;
        rw=T_map.empty;
        constrs=[];
      } in
      BVec.iter self.defs
        ~f:(fun (v,le) ->
            assert (not (T_map.mem v state.rw));
            state.rw <- T_map.add v (norm_le state le) state.rw);
      BVec.iter self.cs
        ~f:(fun (c:Constr.t) ->
            let {Constr.le; op; const; lits} = c in
            let op = match op with
              | Op.Eq -> Eq
              | Op.Leq -> Leq
              | Op.Lt -> Lt
            in
            let c = {le;const;lits;op} in
            add_constr state c
          );
      state

    let rec solve_rec (self:state) : result =
      begin match T_map.choose_opt self.vars with
        | None ->
          let m = Model.empty in
          Sat m (* TODO: model *)

        | Some (t, _) ->
          self.vars <- T_map.remove t self.vars;
          Log.debugf 30
            (fun k->k "(@[intsolver.elim-var@ %a@ :remaining %d@])"
                A.pp_term t (T_map.cardinal self.vars));

          assert false (* TODO *)

      end

  end

  let check (self:t) : result =
    Log.debugf 10 (fun k->k "(@[intsolver.check@])");
    let state = Check_.create self in
    Check_.solve_rec state

  let _check_invariants _ = ()
end
