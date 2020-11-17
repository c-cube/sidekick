

module type ARG = sig
  (** terms *)
  module T : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
    val pp : t Fmt.printer
  end

  type tag
  val pp_tag : tag Fmt.printer
end

module Pred : sig
  type t = Lt | Leq | Geq | Gt | Neq | Eq

  val neg : t -> t
  val pp : t Fmt.printer
  val to_string : t -> string
end = struct
  type t = Lt | Leq | Geq | Gt | Neq | Eq
  let to_string = function
    | Lt -> "<"
    | Leq -> "<="
    | Eq -> "="
    | Neq -> "!="
    | Gt -> ">"
    | Geq -> ">="

  let neg = function
    | Leq -> Gt
    | Lt -> Geq
    | Eq -> Neq
    | Neq -> Eq
    | Geq -> Lt
    | Gt -> Leq

  let pp out p = Fmt.string out (to_string p)
end

module type S = sig
  module A : ARG

  type t

  type term = A.T.t

  module LE : sig
    type t

    val const : Q.t -> t
    val zero : t
    val var : term -> t
    val neg : t -> t

    val find_exn : term -> t -> Q.t
    val find : term -> t -> Q.t option
    val mem : term -> t -> bool

    module Infix : sig
      val (+) : t -> t -> t
      val (-) : t -> t -> t
      val ( * ) : Q.t -> t -> t
    end
    include module type of Infix

    val pp : t Fmt.printer
  end

  (** {3 Arithmetic constraint} *)
  module Constr : sig
    type t

    val pp : t Fmt.printer
    val mk : ?tag:A.tag -> Pred.t -> LE.t -> LE.t -> t
    val is_absurd : t -> bool
  end

  val create : unit -> t

  val assert_c : t -> Constr.t -> unit

  type model

  val get_model : model -> term -> Q.t
  val pp_model : model Fmt.printer

  type res =
    | Sat of model
    | Unsat of A.tag list

  val solve : t -> res
end

module Make(A : ARG)
  : S with module A = A
= struct
  module A = A
  module T = A.T

  module T_set = CCSet.Make(A.T)
  module T_map = CCMap.Make(A.T)

  type term = A.T.t

  module LE = struct
    module M = T_map

    type t = {
      le: Q.t M.t;
      const: Q.t;
    }

    let const x : t = {const=x; le=M.empty}
    let zero = const Q.zero
    let var x : t = {const=Q.zero; le=M.singleton x Q.one}

    let[@inline] find_exn v le = M.find v le.le
    let[@inline] find v le = M.get v le.le
    let[@inline] mem v le = M.mem v le.le

    let[@inline] remove v le : t = {le with le=M.remove v le.le}

    let neg a : t =
      {const=Q.neg a.const;
       le=M.map Q.neg a.le; }

    let (+) a b : t =
      {const = Q.(a.const + b.const);
       le=M.merge_safe a.le b.le
           ~f:(fun _ -> function
               | `Left x | `Right x -> Some x
               | `Both (x,y) ->
                 let z = Q.(x + y) in
                 if Q.sign z = 0 then None else Some z)
      }

    let (-) a b : t =
      {const = Q.(a.const - b.const);
       le=M.merge_safe a.le b.le
           ~f:(fun _ -> function
               | `Left x -> Some x
               | `Right x -> Some (Q.neg x)
               | `Both (x,y) ->
                 let z = Q.(x - y) in
                 if Q.sign z = 0 then None else Some z)
      }

    let ( * ) x a : t =
      if Q.sign x = 0 then const Q.zero
      else (
        {const=Q.( a.const * x );
         le=M.map (fun y -> Q.(x * y)) a.le
        }
      )

    let max_var self : T.t option =
      M.keys self.le |> Iter.max ~lt:(fun a b -> T.compare a b < 0)

    (* ensure coeff of [v] is 1 *)
    let normalize_wrt (v:T.t) le : t =
      let q = find_exn v le in
      Q.inv q * le

    module Infix = struct
      let (+) = (+)
      let (-) = (-)
      let ( * ) = ( * )
    end

    let vars self = T_map.keys self.le

    let pp out (self:t) : unit =
      let pp_pair out (e,q) =
        if Q.equal Q.one q then T.pp out e
        else Fmt.fprintf out "%a * %a" Q.pp_print q T.pp e
      in
      let pp_sum out le =
        (Util.pp_iter ~sep:" + " pp_pair) out (M.to_iter le)
      in
      if Q.sign self.const = 0 then (
        Fmt.fprintf out "(@[%a@])" pp_sum self.le
      ) else (
        Fmt.fprintf out "(@[%a@ + %a@])" Q.pp_print self.const pp_sum self.le
      )
  end

  (** {2 Constraints} *)
  module Constr = struct
    type t = {
      pred: Pred.t;
      le: LE.t;
      tag: A.tag list;
    }

    let pp out (c:t) : unit =
      Fmt.fprintf out "(@[constr@ :le %a@ :pred %s 0@])"
        LE.pp c.le (Pred.to_string c.pred)

    let mk_ ~tag pred le : t = {pred; tag; le; }
    let mk ?tag pred l1 l2 : t =
      mk_ ~tag:(CCOpt.to_list tag) pred LE.(l1 - l2)

    let is_absurd (self:t) : bool =
      T_map.is_empty self.le.le &&
      let c = self.le.const in
      begin match self.pred with
        | Leq -> Q.compare c Q.zero > 0
        | Lt -> Q.compare c Q.zero >= 0
        | Geq -> Q.compare c Q.zero < 0
        | Gt -> Q.compare c Q.zero <= 0
        | Eq -> Q.compare c Q.zero <> 0
        | Neq -> Q.compare c Q.zero = 0
      end

    let is_trivial (self:t) : bool =
      T_map.is_empty self.le.le && not (is_absurd self)

    (* nornalize and return maximum variable *)
    let normalize (self:t) : t =
      match self.pred with
      | Geq -> mk_ ~tag:self.tag Leq (LE.neg self.le)
      | Gt -> mk_ ~tag:self.tag Lt (LE.neg self.le)
      | _ -> self

    let find_max (self:t) : T.t option * bool =
      match LE.max_var self.le with
      | None -> None, true
      | Some t -> Some t, Q.sign (T_map.find t self.le.le) > 0
  end

  (** constraints for a variable (where the variable is maximal) *)
  type c_for_var = {
    occ_pos: Constr.t list;
    occ_eq: Constr.t list;
    occ_neg: Constr.t list;
  }

  type pre_model_strict = Strict | NonStrict
  type pre_model_constr =
    | PM_eq of LE.t
    | PM_bounds of {
        lower: (pre_model_strict * LE.t) list;
        upper: (pre_model_strict * LE.t) list;
      }

  type pre_model = pre_model_constr lazy_t T_map.t
  type model = Q.t T_map.t lazy_t

  type system = {
    empties: Constr.t list; (* no variables, check first *)
    pre_model: pre_model; (* for model construction *)
    idx: c_for_var T_map.t;
    (* map [t] to [cft] where [cft] are normalized constraints whose
       maximum term is [t], with positive sign for [cft.occ_pos]
       and negative for [cft.neg_pos] respectively. *)
  }

  type t = {
    mutable cs: Constr.t list;
    mutable sys: system;
  }

  let empty_sys : system = {empties=[]; pre_model=T_map.empty; idx=T_map.empty}
  let empty_c_for_v : c_for_var =
    { occ_pos=[]; occ_neg=[]; occ_eq=[] }

  let create () : t = {
    cs=[];
    sys=empty_sys;
  }

  let add_sys (sys:system) (c:Constr.t) : system =
    assert (match c.pred with Eq|Leq|Lt -> true | _ -> false);
    if Constr.is_trivial c then (
      Log.debugf 10 (fun k->k"(@[FM.drop-trivial@ %a@])" Constr.pp c);
      sys
    ) else (
      match Constr.find_max c with
      | None, _ -> {sys with empties=c :: sys.empties}
      | Some v, occ_pos ->
        Log.debugf 30 (fun k->k "(@[FM.add-sys %a@ :max_var %a@ :occurs-pos %B@])"
                          Constr.pp c T.pp v occ_pos);
        let cs = T_map.get_or ~default:empty_c_for_v v sys.idx in
        let cs =
          if c.pred = Eq then {cs with occ_eq = c :: cs.occ_eq}
          else if occ_pos then {cs with occ_pos = c :: cs.occ_pos}
          else {cs with occ_neg = c :: cs.occ_neg }
        in
        let idx = T_map.add v cs sys.idx in
        {sys with idx}
    )

  let assert_c (self:t) c0 : unit =
    Log.debugf 10 (fun k->k "(@[FM.add-constr@ %a@ :tags %a@])"
                      Constr.pp c0 (Fmt.Dump.list A.pp_tag) c0.tag);
    let c = Constr.normalize c0 in
    if c.pred <> c0.pred then (
      Log.debugf 30 (fun k->k "(@[FM.normalized %a@])" Constr.pp c);
    );
    assert (match c.pred with Eq | Leq | Lt -> true | _ -> false);
    self.cs <- c :: self.cs;
    self.sys <- add_sys self.sys c;
    ()

  let pp_system out (self:system) : unit =
    let pp_idxkv out (t,{occ_eq; occ_pos; occ_neg}) =
      Fmt.fprintf out
        "(@[for-var %a@ @[:occ-eq %a@]@ @[:occ-pos %a@]@ @[:occ-neg %a@]@])"
        T.pp t
        (Fmt.Dump.list Constr.pp) occ_eq
        (Fmt.Dump.list Constr.pp) occ_pos
        (Fmt.Dump.list Constr.pp) occ_neg
    in
    Fmt.fprintf out "(@[:empties %a@ :idx (@[%a@])@])"
      (Fmt.Dump.list Constr.pp) self.empties
      (Util.pp_iter pp_idxkv) (T_map.to_iter self.idx)

  (* TODO: be able to provide a model for SAT *)
  let build_model_ (self:pre_model) : _ T_map.t =
    let l = T_map.to_iter self |> Iter.to_rev_list in

    let m = ref T_map.empty in

    (* how to evaluate a linexpr in the model *)
    let eval_le (le:LE.t) : Q.t =
      let find x =
        try T_map.find x !m
        with Not_found ->
          m := T_map.add x Q.zero !m; (* remember this choice *)
          Q.zero in
      T_map.to_iter le.LE.le
      |> Iter.fold
        (fun sum (t,coeff) -> Q.(sum + coeff * find t))
        le.LE.const
    in
    let or_strict s1 s2 = match s1, s2 with
      | Strict, _ | _, Strict -> Strict
      | NonStrict, NonStrict -> NonStrict
    in
    let max_pair (s1,q1)(s2,q2) =
      if Q.equal q1 q2 then or_strict s1 s2, q1
      else if Q.gt q1 q2 then s1,q1
      else s2,q2
    and min_pair (s1,q1)(s2,q2) =
      if Q.equal q1 q2 then or_strict s1 s2, q1
      else if Q.lt q1 q2 then s1,q1
      else s2,q2
    in
    List.iter
      begin fun (v,cs_v) ->
        (* update [v] using its constraints [cs_v].
           [m] is the model to update *)
        let val_v =
          match cs_v with
          | lazy (PM_eq le) -> eval_le le
          | lazy (PM_bounds {lower; upper}) ->
            let lower = List.map (fun (s,le) -> s, eval_le le) lower in
            let upper = List.map (fun (s,le) -> s, eval_le le) upper in
            let strict_low, lower = match lower with
              | [] -> NonStrict, Q.minus_inf
              | x :: l -> List.fold_left max_pair x l
            and strict_up, upper = match upper with
              | [] -> NonStrict, Q.inf
              | x :: l -> List.fold_left min_pair x l
            in
            if Q.is_real lower && Q.is_real upper then (
              if Q.equal lower upper then (
                assert (strict_low=NonStrict && strict_up=NonStrict); (* unsat otherwise *)
                lower
              ) else (
                Q.((lower + upper) / of_int 2) (* middle *)
              )
            ) else if Q.is_real lower then (
              if strict_low=Strict then Q.(lower + one) else lower
            ) else if Q.is_real upper then (
              if strict_up=Strict then Q.(upper - one) else upper
            ) else (
              Q.zero (* no bounds *)
            )
        in
        assert (not (T_map.mem v !m)); (* by ordering *)
        m := T_map.add v val_v !m;
      end
      l;
    !m

  let get_model (m:model) (v:T.t) : Q.t =
    let lazy m = m in
    try T_map.find v m
    with Not_found -> Q.zero

  let pp_model out (m:model) : unit =
    let lazy m = m in
    let pp_pair out (v,q) = Fmt.fprintf out "(@[%a@ %a@])" T.pp v Q.pp_print q in
    Fmt.fprintf out "(@[<hv1>model@ %a@])"
      (Util.pp_iter pp_pair) (T_map.to_iter m)

  type res =
    | Sat of model
    | Unsat of A.tag list

  (* replace [x] with [by] inside [le] *)
  let subst_le (x:T.t) (le:LE.t) ~by:(le1:LE.t) : LE.t =
    let q = LE.find_exn x le in
    let le = LE.remove x le in
    LE.( le + q * le1 )

  let subst_constr ~tag x c ~by : Constr.t =
    let open Constr in
    let c = {
      c with
      le=subst_le x ~by c.le;
      tag=tag @ c.tag;
    } in
    Constr.normalize c

  (* given an ineq constraint on [v], canonize it wrt [v]
     (set the coeff of [v] to 1)
     and return whether it's strict or not *)
  let premod_of_constr (v:T.t) (c:Constr.t) : pre_model_strict * LE.t =
    let strict =
      match c.Constr.pred with
      | Pred.Leq -> NonStrict | Pred.Lt -> Strict
      | _ -> assert false
    in
    let coeff =
      try LE.find_exn v c.Constr.le
      with Not_found -> assert false
    in
    let le = LE.remove v c.Constr.le in
    let le = LE.( Q.(one / coeff) * le) in
    strict, le

  let rec solve_ (self:system) : res =
    Log.debugf 50
      (fun k->k "(@[FM.solve-rec@ :sys %a@])" pp_system self);
    begin match List.find Constr.is_absurd self.empties with
      | c ->
        Log.debugf 10 (fun k->k"(@[FM.unsat@ :by-absurd %a@])" Constr.pp c);
        Unsat c.tag
      | exception Not_found ->
        (* need to process biggest variable first *)
        match T_map.max_binding_opt self.idx with
        | None ->
          let m = lazy (build_model_ self.pre_model) in
          Sat m
        | Some (v, {occ_eq=c0 :: ceq'; occ_pos; occ_neg}) ->
          (* at least one equality constraint, use it as a substitution *)

          (* remove [v] from [idx] *)
          let sys = {self with idx=T_map.remove v self.idx} in

          (* substitute using [c0] in the other constraints containing [v] *)
          assert (c0.pred = Eq);
          let l0 = LE.normalize_wrt v c0.le in
          (* turn equation [c0] into [v = rhs] *)
          let rhs = LE.neg @@ LE.remove v l0 in
          Log.debugf 50
            (fun k->k "(@[FM.subst-from-eq@ :v %a@ :rhs %a@])"
                T.pp v LE.pp rhs);

          (* perform substitution in other constraints. Note that [v] cannot
             occur in constraints in the rest of [sys] because it's the
             maximal variable of the system, so it would be the maximum
             variable of these other constraints too.
          *)
          let new_sys =
            [Iter.of_list ceq'; Iter.of_list occ_pos; Iter.of_list occ_neg]
            |> Iter.of_list
            |> Iter.flatten
            |> Iter.map (subst_constr v ~tag:c0.Constr.tag ~by:rhs)
            |> Iter.fold add_sys sys
          in

          let new_sys =
            (* update pre-model, keeping only [v := rhs] *)
            let pre_model = T_map.add v (Lazy.from_val (PM_eq rhs)) self.pre_model in
            {new_sys with pre_model}
          in

          solve_ new_sys

        | Some (v, {occ_eq=[]; occ_pos=l_pos; occ_neg=l_neg}) ->
          Log.debugf 10
            (fun k->k "(@[@{<yellow>FM.pivot@}@ :v %a@ :lpos %a@ :lneg %a@])"
                T.pp v (Fmt.Dump.list Constr.pp) l_pos
                (Fmt.Dump.list Constr.pp) l_neg);

          (* remove [v] *)
          let sys = {self with idx=T_map.remove v self.idx} in

          let new_sys =
            Iter.product (Iter.of_list l_pos) (Iter.of_list l_neg)
            |> Iter.map
              (fun (c1,c2) ->
                let q1 = LE.find_exn v c1.Constr.le in
                let q2 = LE.find_exn v c2.Constr.le in
                assert (Q.sign q1 > 0 && Q.sign q2 < 0);
                let le = LE.( c1.Constr.le + (Q.(q1 / abs q2) * c2.Constr.le) ) in
                Log.debugf 50 (fun k->k "coeff=%a; le: %a" Q.pp_print (Q.inv q1) LE.pp le);
                let pred = match c1.Constr.pred, c2.Constr.pred with
                  | Lt, _ | _, Lt -> Pred.Lt
                  | Leq, Leq -> Pred.Leq
                  | _ ->
                    Log.debugf 1
                      (fun k->k "unexpected pair in pivot@ :c1 %a@ :c2 %a"
                          Constr.pp c1 Constr.pp c2);
                    assert false
                in
                let c = Constr.mk_ ~tag:(c1.tag @ c2.tag) pred le in
                Log.debugf 50 (fun k->k "(@[FM.resolve@ %a@ %a@ :yields@ %a@])"
                                  Constr.pp c1 Constr.pp c2 Constr.pp c);
                assert (not (LE.mem v c.Constr.le));
                c)
            |> Iter.fold add_sys sys
          in

          let new_sys =
            let pre_model =
              let pm_c = lazy (
                let lower = List.rev_map (premod_of_constr v) l_neg in
                let upper = List.rev_map (premod_of_constr v) l_pos in
                PM_bounds {lower; upper}
              ) in
              T_map.add v pm_c self.pre_model
            in
            {new_sys with pre_model}
          in

          solve_ new_sys
    end

  let solve (self:t) : res =
    Log.debugf 5
      (fun k->k"(@[<hv>@{<Green>FM.solve@}@ %a@])" (Util.pp_list Constr.pp) self.cs);
    solve_ self.sys
end

