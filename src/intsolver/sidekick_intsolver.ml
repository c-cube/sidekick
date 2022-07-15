
module type ARG = sig
  module Z : Sidekick_arith.INT_FULL

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

  module ZTbl = CCHashtbl.Make(Z)

  module Utils_ : sig
    type divisor = {
      prime : Z.t;
      power : int;
    }
    val is_prime : Z.t -> bool
    val prime_decomposition : Z.t -> divisor list
    val primes_leq : Z.t -> Z.t Iter.t
  end = struct

    type divisor = {
      prime : Z.t;
      power : int;
    }

    let two = Z.of_int 2

    (* table from numbers to some of their divisor (if any) *)
    let _table = lazy (
      let t = ZTbl.create 256 in
      ZTbl.add t two None;
      t)

    let _divisors n = ZTbl.find (Lazy.force _table) n

    let _add_prime n =
      ZTbl.replace (Lazy.force _table) n None

    (* add to the table the fact that [d] is a divisor of [n] *)
    let _add_divisor n d =
      assert (not (ZTbl.mem (Lazy.force _table) n));
      ZTbl.add (Lazy.force _table) n (Some d)

    (* primality test, modifies _table *)
    let _is_prime n0 =
      let n = ref two in
      let bound = Z.succ (Z.sqrt n0) in
      let is_prime = ref true in
      while !is_prime && Z.(!n <= bound) do
        if Z.(rem n0 !n = zero)
        then begin
          is_prime := false;
          _add_divisor n0 !n;
        end;
        n := Z.succ !n;
      done;
      if !is_prime then _add_prime n0;
      !is_prime

    let is_prime n =
      try
        begin match _divisors n with
          | None -> true
          | Some _ -> false
        end
      with Not_found ->
      if Z.probab_prime n && _is_prime n then (
        _add_prime n; true
      ) else false

    let rec _merge l1 l2 = match l1, l2 with
      | [], _ -> l2
      | _, [] -> l1
      | p1::l1', p2::l2' ->
        match Z.compare p1.prime p2.prime with
        | 0 ->
          {prime=p1.prime; power=p1.power+p2.power} :: _merge l1' l2'
        | n when n < 0 ->
          p1 :: _merge l1' l2
        | _ -> p2 :: _merge l1 l2'

    let rec _decompose n =
      try
        begin match _divisors n with
          | None -> [{prime=n; power=1;}]
          | Some q1 ->
            let q2 = Z.divexact n q1 in
            _merge (_decompose q1) (_decompose q2)
        end
      with Not_found ->
        ignore (_is_prime n);
        _decompose n

    let prime_decomposition n =
      if is_prime n
      then [{prime=n; power=1;}]
      else _decompose n

    let primes_leq n0 k =
      let n = ref two in
      while Z.(!n <= n0) do
        if is_prime !n then k !n
      done
  end [@@warning "-60"]


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
    let mem self t : bool = T_map.mem t self
    let remove self t = T_map.remove t self
    let find_exn self t = T_map.find t self
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
        self empty

    let (+) = merge
    let ( * ) = mult
    let ( ~- ) = neg
    let (-) a b = a + ~- b
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

  (* FIXME: need to simplify: compute gcd(le.coeffs), then divide by that
     and round const appropriately *)

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
    Log.debugf 15 (fun k->k "(@[sidekick.intsolver.assert@ %a@])" Constr.pp c);
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
      | Eq
      | Eq_mod of {
          prime: Z.t;
          pow: int;
        } (* modulo prime^pow *)

    let pp_op out = function
      | Leq -> Fmt.string out "<="
      | Eq -> Fmt.string out "="
      | Eq_mod {prime; pow} -> Fmt.fprintf out "%a^%d" Z.pp prime pow

    type constr = {
      le: LE.t;
      const: Z.t;
      op: op;
      lits: lit Bag.t;
    }

    let pp_constr out self =
      Fmt.fprintf out "(@[%a@ %a %a@])" Linexp.pp self.le pp_op self.op Z.pp self.const

    type state = {
      mutable rw: LE.t T_map.t; (* rewrite rules *)
      mutable vars: int T_map.t; (* variables in at least one constraint *)
      mutable constrs: constr list;
      mutable ok: (unit, constr) Result.t;
    }
    (* main solving state. mutable, but copied for backtracking.
       invariant: variables in [rw] do not occur anywhere else
    *)

    let[@inline] is_ok_ self = CCResult.is_ok self.ok

    (* perform rewriting on the linear expression *)
    let rec norm_le (self:state) (le:LE.t) : LE.t =
      LE.flat_map
        (fun t ->
           begin match T_map.find t self.rw with
             | le -> norm_le self le
             | exception Not_found -> LE.return t
           end)
        le

    let[@inline] count_v self t : int = T_map.get_or ~default:0 t self.vars

    let[@inline] incr_v (self:state) (t:term) : unit =
      self.vars <- T_map.add t (1 + count_v self t) self.vars

    (* GCD of the coefficients of this linear expression *)
    let gcd_coeffs (le:LE.t) : Z.t =
      match T_map.choose_opt le with
      | None -> Z.one
      | Some (_, z0) -> T_map.fold (fun _ z m -> Z.gcd z m) le z0

    let decr_v (self:state) (t:term) : unit =
      let n = count_v self t - 1 in
      assert (n >= 0);
      self.vars <-
        (if n=0 then T_map.remove t self.vars
         else T_map.add t n self.vars)

    let simplify_constr (c:constr) : (constr, unit) Result.t =
      let exception E_unsat in
      try
        match T_map.choose_opt c.le with
        | None -> Ok c
        | Some (_, z0) ->
          let c_gcd = T_map.fold (fun _ z m -> Z.gcd z m) c.le z0 in
          if Z.(c_gcd > one) then (
            let const = match c.op with
              | Leq ->
                (* round down, regardless of sign *)
                Z.ediv c.const c_gcd
              | Eq | Eq_mod _ ->
                if Z.equal (Z.rem c.const c_gcd) Z.zero then (
                  (* compatible constant *)
                  Z.(divexact c.const c_gcd)
                ) else (
                  raise E_unsat
                )
            in

            let c' = {
              c with
              le=T_map.map (fun c -> Z.(c / c_gcd)) c.le;
              const;
            } in
            Log.debugf 50
              (fun k->k "(@[intsolver.simplify@ :from %a@ :into %a@])"
                  pp_constr c pp_constr c');
            Ok c'
          ) else Ok c
      with E_unsat ->
        Log.debugf 50 (fun k->k "(@[intsolver.simplify.unsat@ %a@])" pp_constr c);
        Error ()

    let add_constr (self:state) (c:constr) : unit =
      if is_ok_ self then (
        let c = {c with le=norm_le self c.le } in
        match simplify_constr c with
        | Ok c ->
          Log.debugf 50 (fun k->k "(@[intsolver.add-constr@ %a@])" pp_constr c);
          LE.iter (fun t _ -> incr_v self t) c.le;
          self.constrs <- c :: self.constrs
        | Error () ->
          self.ok <- Error c
      )

    let remove_constr (self:state) (c:constr) : unit =
      LE.iter (fun t _ -> decr_v self t) c.le

    let create (self:t) : state =
      let state = {
        vars=T_map.empty;
        rw=T_map.empty;
        constrs=[];
        ok=Ok();
      } in
      BVec.iter self.defs
        ~f:(fun (v,le) ->
            assert (not (T_map.mem v state.rw));
            (* normalize as much as we can now *)
            let le = norm_le state le in
            Log.debugf 50 (fun k->k "(@[intsolver.add-rw %a@ := %a@])" pp_term v LE.pp le);
            state.rw <- T_map.add v le state.rw);
      BVec.iter self.cs
        ~f:(fun (c:Constr.t) ->
            let {Constr.le; op; const; lits} = c in
            let op, const = match op with
              | Op.Eq -> Eq, const
              | Op.Leq -> Leq, const
              | Op.Lt -> Leq, Z.pred const (* [x < t] is [x <= t-1] *)
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

        | Some (t, _) -> elim_var_ self t
      end


    and elim_var_ self (x:term) : result =
      Log.debugf 20
        (fun k->k "(@[@{<Yellow>intsolver.elim-var@}@ %a@ :remaining %d@])"
            A.pp_term x (T_map.cardinal self.vars));

      assert (not (T_map.mem x self.rw)); (* would have been rewritten away *)
      self.vars <- T_map.remove x self.vars;

      (* gather the sets *)
      let set_e = ref [] in (* eqns *)
      let set_l = ref [] in (* t <= … *)
      let set_g = ref [] in (* t >= … *)
      let set_m = ref [] in (* t = … [n] *)
      let others = ref [] in

      let classify_constr (c:constr) =
        match T_map.get x c.le, c.op with
        | None, _ ->
          others := c :: !others;
        | Some n_t, Leq ->
          if Z.sign n_t > 0 then
            set_l := (n_t,c) :: !set_l
          else
            set_g := (n_t,c) :: !set_g
        | Some n_t, Eq ->
          set_e := (n_t,c) :: !set_e
        | Some n_t, Eq_mod _ ->
          set_m := (n_t,c) :: !set_m
      in

      List.iter classify_constr self.constrs;
      self.constrs <- !others; (* remove all constraints involving [t] *)

      Log.debugf 50
        (fun k->
           let pps = Fmt.Dump.(list @@ pair Z.pp pp_constr) in
           k "(@[intsolver.classify.for %a@ E=%a@ L=%a@ G=%a@ M=%a@])"
             A.pp_term x pps !set_e pps !set_l pps !set_g pps !set_m);

      (* now apply the algorithm *)
      if !set_e <> [] then (
        (* case (a): eliminate via an equality. *)

        (* pick an equality with a small coeff, if possible *)
        let coeff1, c1 =
          Iter.of_list !set_e
          |> Iter.min_exn ~lt:(fun (n1,_)(n2,_) -> Z.(abs n1 < abs n2))
        in

        let le1 = LE.(neg @@ remove c1.le x) in

        Log.debugf 30
          (fun k->k "(@[intsolver.case_a.eqn@ :coeff %a@ :c %a@])"
              Z.pp coeff1 pp_constr c1);

        let elim_in_constr (coeff2, c2) =
          let le2 = LE.(neg @@ remove c2.le x) in

          let gcd12 = Z.gcd coeff1 coeff2 in
          (* coeff1 × p1 = coeff2 × p2 = lcm = coeff1 × coeff2 / gcd,
             because coeff1 × coeff2 = lcm × gcd *)
          let lcm12 = Z.(abs coeff1 * abs coeff2 / gcd12) in
          let p1 = Z.(lcm12 / coeff1) in
          let p2 = Z.(lcm12 / coeff2) in
          Log.debugf 50
            (fun k->k "(@[intsolver.elim-in-constr@ %a@ :gcd %a :lcm %a@ :p1 %a :p2 %a@])"
                pp_constr c2 Z.pp gcd12 Z.pp lcm12 Z.pp p1 Z.pp p2);

          let c' =
            let lits = Bag.append c1.lits c2.lits in
            if Z.sign coeff1 <> Z.sign coeff2 then (
              let le' = LE.(p1 * le1 + p2 * le2) in
              let const' = Z.(p1 * c1.const + p2 * c2.const) in
              {op=c2.op; le=le'; const=const'; lits}
            ) else (
              let le' = LE.(p1 * le1 - p2 * le2) in
              let const' = Z.(p1 * c1.const - p2 * c2.const) in
              let le', const' =
                if Z.sign coeff1 < 0 then LE.neg le', Z.neg const'
                else le', const'
              in
              {op=c2.op; le=le'; const=const'; lits}
            )
          in
          add_constr self c'

          (* also add a divisibility constraint if needed *)
          (* TODO:
          if Z.(p1 > one) then (
             let c' = {le=le2; op=Eq_mod p1; const=c2.const} in
             add_constr self c'
          )
         *)
        in
        List.iter elim_in_constr !set_l;
        List.iter elim_in_constr !set_g;
        List.iter elim_in_constr !set_m;

        (* FIXME: handle the congruence *)
      ) else if !set_l = [] || !set_g = [] then (
        (* case (b): no bound on at least one side *)
        assert (!set_e=[]);

        () (* FIXME: handle the congruence *)
      ) else (
        (* case (c): combine inequalities pairwise *)

        let elim_pair (coeff1, c1) (coeff2, c2) : unit =
          assert (Z.sign coeff1 > 0 && Z.sign coeff2 < 0);

          let le1 = LE.remove c1.le x in
          let le2 = LE.remove c2.le x in

          let gcd12 = Z.gcd coeff1 coeff2 in
          let lcm12 = Z.(coeff1 * abs coeff2 / gcd12) in

          let p1 = Z.(lcm12 / coeff1) in
          let p2 = Z.(lcm12 / Z.abs coeff2) in

          Log.debugf 50
            (fun k->k "(@[intsolver.case-b.elim-pair@ L=%a@ G=%a@ \
                       :gcd %a :lcm %a@ :p1 %a :p2 %a@])"
                pp_constr c1 pp_constr c2 Z.pp gcd12 Z.pp lcm12 Z.pp p1 Z.pp p2);

          let new_ineq =
            let le = LE.(p2 * le1 - p1 * le2) in
            let const = Z.(p2 * c1.const - p1 * c2.const) in
            let lits = Bag.append c1.lits c2.lits in
            {op=Leq; le; const; lits}
          in

          add_constr self new_ineq;
          (* TODO: handle modulo constraints *)

        in

        List.iter (fun x1 -> List.iter (elim_pair x1) !set_g) !set_l;
      );

      (* now recurse *)
      solve_rec self
  end

  let check (self:t) : result =

    Log.debugf 10 (fun k->k "(@[@{<Yellow>intsolver.check@}@])");
    let state = Check_.create self in
    Log.debugf 10
      (fun k->k "(@[intsolver.check.stat@ :n-vars %d@ :n-constr %d@])"
          (T_map.cardinal state.vars) (List.length state.constrs));

    match state.ok with
    | Ok () ->
      Check_.solve_rec state
    | Error c ->
      Log.debugf 10 (fun k->k "(@[insolver.unsat-constraint@ %a@])" Check_.pp_constr c);
      (* TODO proper certificate *)
      Unsat ()

  let _check_invariants _ = ()
end
