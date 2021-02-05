(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

(* OPTIMS:
 * - distinguish separate systems (that do not interact), such as in { 1 <= 3x = 3y <= 2; z <= 3} ?
 * - Implement gomorry cuts ?
*)

module Fmt = CCFormat
module type VAR = Linear_expr_intf.VAR
module type FRESH = Linear_expr_intf.FRESH
module type VAR_GEN = Linear_expr_intf.VAR_GEN

module type S = Simplex_intf.S
module type S_FULL = Simplex_intf.S_FULL

module Vec = CCVector

module Matrix : sig
  type 'a t

  val create : unit -> 'a t
  val get : 'a t -> int -> int -> 'a
  val set : 'a t -> int -> int -> 'a -> unit
  val get_row : 'a t -> int -> 'a Vec.vector
  val copy : 'a t -> 'a t
  val n_row : _ t -> int
  val n_col : _ t -> int
  val push_row : 'a t -> 'a -> unit (* new row, filled with element *)
  val push_col : 'a t -> 'a -> unit (* new column, filled with element *)

  (**/**)
  val check_invariants : _ t -> bool
  (**/**)
end = struct
  type 'a t = {
    mutable n_col: int; (* num of columns *)
    tab: 'a Vec.vector Vec.vector;
  }

  let[@inline] create() : _ = {tab=Vec.create(); n_col=0}

  let[@inline] get m i j = Vec.get (Vec.get m.tab i) j
  let[@inline] get_row m i = Vec.get m.tab i
  let[@inline] set (m:_ t) i j x = Vec.set (Vec.get m.tab i) j x
  let[@inline] copy m = {m with tab=Vec.map Vec.copy m.tab}

  let[@inline] n_row m = Vec.length m.tab
  let[@inline] n_col m = m.n_col

  let push_row m x = Vec.push m.tab (Vec.make (n_col m) x)
  let push_col m x =
    m.n_col <- m.n_col + 1;
    Vec.iter (fun row -> Vec.push row x) m.tab

  let check_invariants m = Vec.for_all (fun r -> Vec.length r = n_col m) m.tab
end

(* use non-polymorphic comparison ops *)
open CCInt.Infix

(* Simplex Implementation *)
module Make_inner
    (Var: VAR)
    (VMap : CCMap.S with type key=Var.t)
    (Param: sig type t val copy : t -> t end)
= struct
  module Var_map = VMap
  module M = Var_map

  type param = Param.t
  type var = Var.t
  type lit = Var.lit

  type erat = {
    base: Q.t; (* reference number *)
    eps_factor: Q.t; (* coefficient for epsilon, the infinitesimal *)
  }

  (** Epsilon-rationals, used for strict bounds *)
  module Erat = struct
    type t = erat

    let zero : t = {base=Q.zero; eps_factor=Q.zero}

    let[@inline] make base eps_factor : t = {base; eps_factor}
    let[@inline] base t = t.base
    let[@inline] eps_factor t = t.eps_factor
    let[@inline] mul k e = make Q.(k * e.base) Q.(k * e.eps_factor)
    let[@inline] sum e1 e2 = make Q.(e1.base + e2.base) Q.(e1.eps_factor + e2.eps_factor)
    let[@inline] compare e1 e2 = match Q.compare e1.base e2.base with
      | 0 -> Q.compare e1.eps_factor e2.eps_factor
      | x -> x

    let lt a b = compare a b < 0
    let gt a b = compare a b > 0

    let[@inline] min x y = if compare x y <= 0 then x else y
    let[@inline] max x y = if compare x y >= 0 then x else y

    let[@inline] evaluate (epsilon:Q.t) (e:t) : Q.t = Q.(e.base + epsilon * e.eps_factor)

    let pp out e =
      if Q.equal Q.zero (eps_factor e)
      then Q.pp_print out (base e)
      else
        Fmt.fprintf out "(@[<h>%a + @<1>ε * %a@])"
          Q.pp_print (base e) Q.pp_print (eps_factor e)
  end

  let str_of_var = Fmt.to_string Var.pp
  let str_of_erat = Fmt.to_string Erat.pp
  let str_of_q = Fmt.to_string Q.pp_print

  type bound = {
    value : Erat.t;
    reason : lit option;
  }

  (* state associated with a variable *)
  type var_state = {
    var: var;
    mutable assign: Erat.t option; (* current assignment *)
    mutable l_bound: bound; (* lower bound *)
    mutable u_bound: bound; (* upper bound *)
    mutable idx_basic: int; (* index in [t.nbasic] *)
    mutable idx_nbasic: int; (* index in [t.nbasic] *)
  }

  (* Exceptions *)
  exception Unsat of var_state
  exception AbsurdBounds of var_state
  exception NoneSuitable

  type basic_var = var_state
  type nbasic_var = var_state

  type t = {
    param: param;
    mutable var_states: var_state M.t; (* var -> its state *)
    tab : Q.t Matrix.t; (* the matrix of coefficients *)
    basic : basic_var Vec.vector; (* basic variables *)
    nbasic : nbasic_var Vec.vector; (* non basic variables *)
  }

  type cert = {
    cert_var: var;
    cert_expr: (Q.t * var) list;
  }

  type res =
    | Solution of Q.t Var_map.t
    | Unsatisfiable of cert

  let create param : t = {
    param;
    var_states = M.empty;
    tab = Matrix.create ();
    basic = Vec.create ();
    nbasic = Vec.create ();
  }

  let[@inline] index_basic (x:basic_var) : int = x.idx_basic
  let[@inline] index_nbasic (x:nbasic_var) : int = x.idx_nbasic

  let[@inline] is_basic (x:var_state) : bool = x.idx_basic >= 0
  let[@inline] is_nbasic (x:var_state) : bool = x.idx_nbasic >= 0

  (* check invariants, for test purposes *)
  let check_invariants (t:t) : bool =
    Matrix.check_invariants t.tab &&
    Vec.for_all (fun v -> is_basic v) t.basic &&
    Vec.for_all (fun v -> is_nbasic v) t.nbasic &&
    Vec.for_all (fun v -> not (is_nbasic v)) t.basic &&
    Vec.for_all (fun v -> not (is_basic v)) t.nbasic &&
    Vec.for_all (fun v -> CCOpt.is_some v.assign) t.nbasic &&
    Vec.for_all (fun v -> CCOpt.is_none v.assign) t.basic &&
    true

  (* find the definition of the basic variable [x],
     as a linear combination of non basic variables *)
  let find_expr_basic_opt t (x:var_state) : Q.t Vec.vector option =
    begin match index_basic x with
      | -1 -> None
      | i -> Some (Matrix.get_row t.tab i)
    end

  (* expression that defines a basic variable in terms of non-basic variables *)
  let find_expr_basic t (x:basic_var) : Q.t Vec.vector =
    let i = index_basic x in
    assert (i >= 0);
    Matrix.get_row t.tab i

  (* build the expression [y = \sum_i (if x_i=y then 1 else 0)·x_i] *)
  let find_expr_nbasic t (x:nbasic_var) : Q.t Vec.vector =
    Vec.map
      (fun y -> if x == y then Q.one else Q.zero)
      t.nbasic

  (* find expression of [x] *)
  let find_expr_total (t:t) (x:var_state) : Q.t Vec.vector =
    match find_expr_basic_opt t x with
    | Some e -> e
    | None ->
      assert (is_nbasic x);
      find_expr_nbasic t x

  (* compute value of basic variable.
     It can be computed by using [x]'s definition
     in terms of nbasic variables, which have values *)
  let value_basic (t:t) (x:basic_var) : Erat.t =
    assert (is_basic x);
    let res = ref Erat.zero in
    let expr = find_expr_basic t x in
    for i = 0 to Vec.length expr - 1 do
      let val_nbasic_i =
        match (Vec.get t.nbasic i).assign with
        | None -> assert false
        | Some e -> e
      in
      res := Erat.sum !res (Erat.mul (Vec.get expr i) val_nbasic_i)
    done;
    !res

  (* extract a value for [x] *)
  let[@inline] value (t:t) (x:var_state) : Erat.t =
    match x.assign with
    | Some e -> e
    | None -> value_basic t x

  (* trivial bounds *)
  let empty_bounds : bound * bound =
    { value = Erat.make Q.minus_inf Q.zero; reason = None; },
    { value = Erat.make Q.inf Q.zero; reason = None; }

  (* find bounds of [x] *)
  let[@inline] get_bounds (x:var_state) : bound * bound =
    x.l_bound, x.u_bound

  let[@inline] get_bounds_values (x:var_state) : Erat.t * Erat.t =
    let l, u = get_bounds x in
    l.value, u.value

  (* is [value x] within the bounds for [x]? *)
  let is_within_bounds (t:t) (x:var_state) : bool * Erat.t =
    let v = value t x in
    let low, upp = get_bounds_values x in
    if Erat.compare v low < 0 then
      false, low
    else if Erat.compare v upp > 0 then
      false, upp
    else
      true, v

  (* add [v] as a non-basic variable, or return its state if already mapped *)
  let get_var_or_add_as_nbasic (t:t) (v:var) : var_state =
    match M.get v t.var_states with
    | Some v -> v
    | None ->
      let l_bound, u_bound = empty_bounds in
      let idx_nbasic = Vec.length t.nbasic in
      let vs = {
        var=v; l_bound; u_bound;
        assign=Some Erat.zero;
        idx_nbasic; idx_basic=(-1);
      } in
      t.var_states <- M.add v vs t.var_states;
      Vec.push t.nbasic vs;
      Matrix.push_col t.tab Q.zero; (* new empty column *)
      vs

  (* add new variables as nbasic variables, return them, ignore
     the already existing variables *)
  let add_vars_as_nbasic (t:t) (l:var list) : unit =
    List.iter
      (fun x ->
         if not (M.mem x t.var_states) then  (
           (* allocate new index for [x] *)
           ignore (get_var_or_add_as_nbasic t x : var_state)
         ))
      l

  (* define basic variable [x] by [eq] in [t] *)
  let add_eq (t:t) (x, eq : var * _ list) : unit =
    let eq = List.map (fun (coeff,x) -> coeff, get_var_or_add_as_nbasic t x) eq in
    (* add [x] as a basic var *)
    begin match M.get x t.var_states with
      | Some _ ->
        invalid_arg (Fmt.sprintf "Variable `%a` already defined." Var.pp x);
      | None ->
        let l_bound, u_bound = empty_bounds in
        let idx_basic = Vec.length t.basic in
        let vs = {
          var=x; l_bound; u_bound; assign=None; idx_basic;
          idx_nbasic=(-1);
        } in
        Vec.push t.basic vs;
        t.var_states <- M.add x vs t.var_states;
    end;
    (* add new row for defining [x] *)
    assert (Matrix.n_col t.tab > 0);
    Matrix.push_row t.tab Q.zero;
    let row_i = Matrix.n_row t.tab - 1 in
    assert (row_i >= 0);

    (* now put into the row the coefficients corresponding to [eq],
       expanding basic variables to their definition *)
    List.iter
      (fun (c, x) ->
         (* FIXME(perf): replace with a `idx -> Q.t` function, do not allocate vector *)
         let expr = find_expr_total t x in
         assert (Vec.length expr = Matrix.n_col t.tab);
         Vec.iteri
           (fun j c' ->
              if not (Q.equal Q.zero c') then (
                Matrix.set t.tab row_i j Q.(Matrix.get t.tab row_i j + c * c')
              ))
           expr)
      eq;
    ()

  (* add bounds to [x] in [t] *)
  let add_bound_aux (x:var_state)
      (low:Erat.t) (low_reason:lit option)
      (upp:Erat.t) (upp_reason:lit option) : unit =
    let l, u = get_bounds x in
    let l' = if Erat.lt low l.value then l else { value = low; reason = low_reason; } in
    let u' = if Erat.gt upp u.value then u else { value = upp; reason = upp_reason; } in
    x.l_bound <- l';
    x.u_bound <- u';
    ()

  let add_bounds (t:t)
      ?strict_lower:(slow=false) ?strict_upper:(supp=false)
      ?lower_reason ?upper_reason (x, l, u) : unit =
    let x = get_var_or_add_as_nbasic t x in
    let e1 = if slow then Q.one else Q.zero in
    let e2 = if supp then Q.neg Q.one else Q.zero in
    add_bound_aux x (Erat.make l e1) lower_reason (Erat.make u e2) upper_reason;
    if is_nbasic x then (
      let b, v = is_within_bounds t x in
      if not b then (
        x.assign <- Some v;
      )
    )

  let add_lower_bound t ?strict ~reason x l =
    add_bounds t ?strict_lower:strict ~lower_reason:reason (x,l,Q.inf)

  let add_upper_bound t ?strict ~reason x u =
    add_bounds t ?strict_upper:strict ~upper_reason:reason (x,Q.minus_inf,u)

  let iter_all_vars (t:t) : var_state Iter.t =
    Iter.append (Vec.to_iter t.nbasic) (Vec.to_iter t.basic)

  (* full assignment *)
  let full_assign (t:t) : (var * Erat.t) Iter.t =
    Iter.append (Vec.to_iter t.nbasic) (Vec.to_iter t.basic)
    |> Iter.map (fun x -> x.var, value t x)

  let[@inline] min x y = if Q.compare x y < 0 then x else y

  (* Find an epsilon that is small enough for finding a solution, yet
     it must be positive.

     {!Erat.t} values are used to turn strict bounds ([X > 0]) into
     non-strict bounds ([X >= 0 + ε]), because the simplex algorithm
     only deals with non-strict bounds.
     When a solution is found, we need to turn {!Erat.t} into {!Q.t} by
     finding a rational value that is small enough that it will fit into
     all the intervals of [t]. This rational will be the actual value of [ε].
  *)
  let solve_epsilon (t:t) : Q.t =
    let emax =
      Iter.fold
        (fun emax x ->
           let { value = {base=low;eps_factor=e_low}; _} = x.l_bound in
           let { value = {base=upp;eps_factor=e_upp}; _} = x.u_bound in
           let {base=v; eps_factor=e_v} = value t x in
           (* lower bound *)
           let emax =
             if Q.compare low Q.minus_inf > 0 && Q.compare e_v e_low < 0
             then min emax Q.((low - v) / (e_v - e_low))
             else emax
           in
           (* upper bound *)
           if Q.compare upp Q.inf < 0 && Q.compare e_v e_upp > 0
           then min emax Q.((upp - v) / (e_v - e_upp))
           else emax)
        Q.inf (iter_all_vars t)
    in
    if Q.compare emax Q.one >= 0 then Q.one else emax

  let get_full_assign_seq (t:t) : _ Iter.t =
    let e = solve_epsilon t in
    let f = Erat.evaluate e in
    full_assign t
    |> Iter.map (fun (x,v) -> x, f v)

  let get_full_assign t : Q.t Var_map.t = Var_map.of_iter (get_full_assign_seq t)

  (* Find nbasic variable suitable for pivoting with [x].
     A nbasic variable [y] is suitable if it "goes into the right direction"
     (its coefficient in the definition of [x] is of the adequate sign)
     and if it hasn't reached its bound in this direction.

     precondition: [x] is a basic variable whose value in current assignment
       is outside its bounds

     We return the smallest (w.r.t Var.compare) suitable variable.
     This is important for termination.
  *)
  let find_suitable_nbasic_for_pivot (t:t) (x:basic_var) : nbasic_var * Q.t =
    Profile.with_ "simplex.find-pivot-var" @@ fun () ->
    assert (is_basic x);
    let _, v = is_within_bounds t x in
    let b = Erat.compare (value t x) v < 0 in
    (* is nbasic var [y], with coeff [a] in definition of [x], suitable? *)
    let test (y:nbasic_var) (a:Q.t) : bool =
      assert (is_nbasic y);
      let v = value t y in
      let low, upp = get_bounds_values y in
      if b then (
        (Erat.lt v upp && Q.compare a Q.zero > 0) ||
        (Erat.gt v low && Q.compare a Q.zero < 0)
      ) else (
        (Erat.gt v low && Q.compare a Q.zero > 0) ||
        (Erat.lt v upp && Q.compare a Q.zero < 0)
      )
    in
    let nbasic_vars = t.nbasic in
    let expr = find_expr_basic t x in
    (* find best suitable variable *)
    let rec aux i =
      if i = Vec.length nbasic_vars then (
        assert (i = Vec.length expr);
        None
      ) else (
        let y = Vec.get nbasic_vars i in
        let a = Vec.get expr i in
        if test y a then (
          (* see if other variables are better suited *)
          begin match aux (i+1) with
            | None -> Some (y,a)
            | Some (z, _) as res_tail ->
              if Var.compare y.var z.var <= 0
              then Some (y,a)
              else res_tail
          end
        ) else (
          aux (i+1)
        )
      )
    in
    begin match aux 0 with
      | Some res -> res
      | None ->  raise NoneSuitable
    end

  (* pivot to exchange [x] and [y] *)
  let pivot (t:t) (x:basic_var) (y:nbasic_var) (a:Q.t) : unit =
    Profile.with_ "simplex.pivot" @@ fun () ->
    (* swap values ([x] becomes assigned) *)
    let val_x = value t x in
    y.assign <- None;
    x.assign <- Some val_x;
    (* Matrix Pivot operation *)
    let kx = index_basic x in
    let ky = index_nbasic y in
    for j = 0 to Vec.length t.nbasic - 1 do
      if y == Vec.get t.nbasic j then (
        Matrix.set t.tab kx j Q.(inv a)
      ) else (
        Matrix.set t.tab kx j Q.(neg (Matrix.get t.tab kx j) / a)
      )
    done;
    for i = 0 to Vec.length t.basic - 1 do
      if i <> kx then (
        let c = Matrix.get t.tab i ky in
        Matrix.set t.tab i ky Q.zero;
        for j = 0 to Vec.length t.nbasic - 1 do
          Matrix.set t.tab i j Q.(Matrix.get t.tab i j + c * Matrix.get t.tab kx j)
        done
      )
    done;
    (* Switch x and y in basic and nbasic vars *)
    Vec.set t.basic kx y;
    Vec.set t.nbasic ky x;
    x.idx_basic <- -1;
    y.idx_basic <- kx;
    x.idx_nbasic <- ky;
    y.idx_nbasic <- -1;
    ()

  (* find minimum element of [arr] (wrt [cmp]) that satisfies predicate [f] *)
  let find_min_filter ~cmp (f:'a -> bool) (arr:('a,_) Vec.t) : 'a option =
    (* find the first element that satisfies [f] *)
    let rec aux_find_first i =
      if i = Vec.length arr then None
      else (
        let x = Vec.get arr i in
        if f x
        then aux_compare_with x (i+1)
        else aux_find_first (i+1)
      )
    (* find if any element of [l] satisfies [f] and is smaller than [x] *)
    and aux_compare_with x i =
      if i = Vec.length arr then Some x
      else (
        let y = Vec.get arr i in
        let best = if f y && cmp y x < 0 then y else x in
        aux_compare_with best (i+1)
      )
    in
    aux_find_first 0

  (* check bounds *)
  let check_bounds (t:t) : unit =
    iter_all_vars t
      (fun x ->
         let l = x.l_bound in
         let u = x.u_bound in
         if Erat.gt l.value u.value then raise (AbsurdBounds x))

  let[@inline] compare_by_var x y = Var.compare x.var y.var

  (* actual solving algorithm *)
  let solve_aux (t:t) : unit =
    Profile.instant
      (Printf.sprintf "(simplex.solve :basic %d :non-basic %d)"
         (Vec.length t.basic) (Vec.length t.nbasic));
    check_bounds t;
    (* select the smallest basic variable that is not satisfied in the current
       assignment. *)
    let rec aux_select_basic_var () =
      match
        Profile.with_ "simplex.select-basic-var" @@ fun () ->
        find_min_filter ~cmp:compare_by_var
          (fun x -> not (fst (is_within_bounds t x)))
          t.basic
      with
        | Some x -> aux_pivot_on_basic x
        | None -> ()
    (* remove the basic variable *)
    and aux_pivot_on_basic x =
      let _b, v = is_within_bounds t x in
      assert (not _b);
      match find_suitable_nbasic_for_pivot t x with
        | y, a ->
          (* exchange [x] and [y] by pivoting *)
          pivot t x y a;
          (* assign [x], now a nbasic variable, to the faulty bound [v] *)
          x.assign <- Some v;
          (* next iteration *)
          aux_select_basic_var ()
        | exception NoneSuitable ->
          raise (Unsat x)
    in
    aux_select_basic_var ();
    ()

  (* main method for the user to call *)
  let solve (t:t) : res =
    try
      solve_aux t;
      Solution (get_full_assign t)
    with
      | Unsat x ->
        let cert_expr =
          List.combine
            (Vec.to_list (find_expr_basic t x))
            (Vec.to_list t.nbasic |> CCList.map (fun x -> x.var))
        in
        Unsatisfiable { cert_var=x.var; cert_expr; } (* FIXME *)
      | AbsurdBounds x ->
        Unsatisfiable { cert_var=x.var; cert_expr=[]; }

  (* add [c·x] to [m] *)
  let add_expr_ (x:var) (c:Q.t) (m:Q.t M.t) =
    let c' = M.get_or ~default:Q.zero x m in
    let c' = Q.(c + c') in
    if Q.equal Q.zero c' then M.remove x m else M.add x c' m

  (* dereference basic variables from [c·x], and add the result to [m] *)
  let rec deref_var_ t x c m =
    match find_expr_basic_opt t x with
    | None -> add_expr_ x.var c m
    | Some expr_x ->
      let m = ref m in
      Vec.iteri
        (fun i c_i ->
           let y_i = Vec.get t.nbasic i in
           m := deref_var_ t y_i Q.(c * c_i) !m)
        expr_x;
      !m

  (* maybe invert bounds, if [c < 0] *)
  let scale_bounds c (l,u) : bound * bound =
    match Q.compare c Q.zero with
      | 0 ->
        let b = { value = Erat.zero; reason = None; } in
        b, b
      | n when n<0 ->
        { u with value = Erat.mul c u.value; },
        { l with value = Erat.mul c l.value; }
      | _ ->
        { l with value = Erat.mul c l.value; },
        { u with value = Erat.mul c u.value; }

  let add_to_unsat_core acc = function
    | None -> acc
    | Some reason -> reason :: acc

  let check_cert (t:t) (c:cert) =
    let x = M.get c.cert_var t.var_states |> CCOpt.get_lazy (fun()->assert false) in
    let { value = low_x; reason = low_x_reason; } = x.l_bound in
    let { value = up_x; reason = upp_x_reason; } = x.u_bound in
    begin match c.cert_expr with
      | [] ->
        if Erat.compare low_x up_x > 0
        then `Ok (add_to_unsat_core (add_to_unsat_core [] low_x_reason) upp_x_reason)
        else `Bad_bounds (str_of_erat low_x, str_of_erat up_x)
      | expr ->
        let e0 = deref_var_ t x (Q.neg Q.one) M.empty in
        (* compute bounds for the expression [c.cert_expr],
           and also compute [c.cert_expr - x] to check if it's 0] *)
        let low, low_unsat_core, up, up_unsat_core, expr_minus_x =
          List.fold_left
            (fun (l, luc, u, uuc, expr_minus_x) (c, y) ->
               let y = M.get y t.var_states |> CCOpt.get_lazy (fun ()->assert false) in
               let ly, uy = scale_bounds c (get_bounds y) in
               assert (Erat.compare ly.value uy.value <= 0);
               let expr_minus_x = deref_var_ t y c expr_minus_x in
               let luc = add_to_unsat_core luc ly.reason in
               let uuc = add_to_unsat_core uuc uy.reason in
               Erat.sum l ly.value, luc, Erat.sum u uy.value, uuc, expr_minus_x)
            (Erat.zero, [], Erat.zero, [], e0)
            expr
        in
        (* check that the expanded expression is [x], and that
           one of the bounds on [x] is incompatible with bounds of [c.cert_expr] *)
        if M.is_empty expr_minus_x then (
          if Erat.compare low_x up > 0
          then `Ok (add_to_unsat_core up_unsat_core low_x_reason)
          else if Erat.compare up_x low < 0
          then `Ok (add_to_unsat_core low_unsat_core upp_x_reason)
          else `Bad_bounds (str_of_erat low, str_of_erat up)
        ) else `Diff_not_0 expr_minus_x
    end

  (* printer *)

  let matrix_pp_width = ref 8

  let fmt_head = format_of_string "|%*s|| "
  let fmt_cell = format_of_string "%*s| "

  let pp_cert out (c:cert) = match c.cert_expr with
    | [] -> Fmt.fprintf out "(@[inconsistent-bounds %a@])" Var.pp c.cert_var
    | _ ->
      let pp_pair = Fmt.(hvbox ~i:2 @@ pair ~sep:(return "@ * ") Q.pp_print Var.pp) in
      Fmt.fprintf out "(@[<hv>cert@ :var %a@ :linexp %a@])"
        Var.pp c.cert_var
        Fmt.(within "[" "]" @@ hvbox @@ list ~sep:(return "@ + ") pp_pair)
        c.cert_expr

  let pp_mat out t =
    let open Fmt in
    fprintf out "@[<v>";
    (* header *)
    fprintf out fmt_head !matrix_pp_width "";
    Vec.iter (fun x -> fprintf out fmt_cell !matrix_pp_width (str_of_var x.var)) t.nbasic;
    fprintf out "@,";
    (* rows *)
    for i=0 to Matrix.n_row t.tab-1 do
      if i>0 then fprintf out "@,";
      let v = Vec.get t.basic i in
      fprintf out fmt_head !matrix_pp_width (str_of_var v.var);
      let row = Matrix.get_row t.tab i in
      Vec.iter (fun q -> fprintf out fmt_cell !matrix_pp_width (str_of_q q)) row;
    done;
    fprintf out "@]"

  let pp_vars =
    let ppv out v =
      Fmt.fprintf out "(@[var %a@ :assign %a@ :lbound %a@ :ubound %a@])"
        Var.pp v.var (Fmt.Dump.option Erat.pp) v.assign
        Erat.pp v.l_bound.value Erat.pp v.u_bound.value
    in
    Fmt.(within "(" ")" @@ hvbox @@ iter ppv)

  let pp_full_state out (t:t) : unit =
    (* print main matrix *)
    Fmt.fprintf out
      "(@[<hv>simplex@ :n-row %d :n-col %d@ :mat %a@ :vars %a @])"
      (Matrix.n_row t.tab) (Matrix.n_col t.tab) pp_mat t
      pp_vars (iter_all_vars t)
end

module Make(Var:VAR) =
  Make_inner(Var)(CCMap.Make(Var))(struct
    type t = unit
    let copy ()=()
  end)

module Make_full_for_expr(V : VAR_GEN)
    (L : Linear_expr.S
     with type Var.t = V.t
      and type C.t = Q.t
      and type Var.lit = V.lit)
  : S_FULL with type var = V.t
            and type lit = V.lit
            and module L = L
            and module Var_map = L.Var_map
            and type L.var = V.t
            and type L.Comb.t = L.Comb.t
            and type param = V.Fresh.t
= struct
  include Make_inner(V)(L.Var_map)(V.Fresh)
  module L = L

  type op = Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  type constr = L.Constr.t

  (* add a constraint *)
  let add_constr (t:t) (c:constr) (reason:lit) : unit =
    let e, op, q = L.Constr.split c in
    match L.Comb.as_singleton e with
    | Some (c0, x0) ->
      (* no need for a fresh variable, just add constraint on [x0] *)
      let q = Q.div q c0 in
      let op = if Q.sign c0 < 0 then Predicate.neg_sign op else op in
      begin match op with
        | Leq -> add_upper_bound t ~strict:false ~reason x0 q
        | Geq -> add_lower_bound t ~strict:false ~reason x0 q
        | Lt -> add_upper_bound t ~strict:true ~reason x0 q
        | Gt -> add_lower_bound t ~strict:true ~reason x0 q
        | Eq -> add_bounds t (x0,q,q)
                  ~strict_lower:false ~strict_upper:false
                  ~lower_reason:reason ~upper_reason:reason
        | Neq -> assert false
      end
    | None ->
      let (x:var) = V.Fresh.fresh t.param in
      add_eq t (x, L.Comb.to_list e);
      begin match op with
        | Leq -> add_upper_bound t ~strict:false ~reason x q
        | Geq -> add_lower_bound t ~strict:false ~reason x q
        | Lt -> add_upper_bound t ~strict:true ~reason x q
        | Gt -> add_lower_bound t ~strict:true ~reason x q
        | Eq -> add_bounds t (x,q,q)
                  ~strict_lower:false ~strict_upper:false
                  ~lower_reason:reason ~upper_reason:reason
        | Neq -> assert false
      end
end

module Make_full(V : VAR_GEN)
  : S_FULL with type var = V.t
            and type lit = V.lit
            and type L.var = V.t
            and type param = V.Fresh.t
  = Make_full_for_expr(V)(Linear_expr.Make(struct include Q let pp = pp_print end)(V))
