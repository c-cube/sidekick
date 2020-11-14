(*
  copyright (c) 2014-2018, Guillaume Bury, Simon Cruanes
  *)

(* OPTIMS:
 * - distinguish separate systems (that do not interact), such as in { 1 <= 3x = 3y <= 2; z <= 3} ?
 * - Implement gomorry cuts ?
*)

open Containers

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
open Int.Infix

(* Simplex Implementation *)
module Make_inner
    (Var: VAR)
    (VMap : CCMap.S with type key=Var.t)
    (Param: sig type t val copy : t -> t end)
= struct
  module Var_map = VMap
  module M = Var_map

  (* Exceptions *)
  exception Unsat of Var.t
  exception AbsurdBounds of Var.t
  exception NoneSuitable

  type param = Param.t
  type var = Var.t
  type lit = Var.lit

  type basic_var = var
  type nbasic_var = var

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
        Format.fprintf out "(@[<h>%a + @<1>ε * %a@])"
          Q.pp_print (base e) Q.pp_print (eps_factor e)
  end

  let str_of_var = Format.to_string Var.pp
  let str_of_erat = Format.to_string Erat.pp
  let str_of_q = Format.to_string Q.pp_print

  type t = {
    param: param;
    tab : Q.t Matrix.t; (* the matrix of coefficients *)
    basic : basic_var Vec.vector; (* basic variables *)
    nbasic : nbasic_var Vec.vector; (* non basic variables *)
    mutable assign : Erat.t M.t; (* assignments *)
    mutable bounds : (Erat.t * Erat.t) M.t; (* (lower, upper) bounds for variables *)
    mutable idx_basic : int M.t; (* basic var -> its index in [basic] *)
    mutable idx_nbasic : int M.t; (* non basic var -> its index in [nbasic] *)
  }

  type cert = {
    cert_var: var;
    cert_expr: (Q.t * var) list;
    cert_core: lit list;
  }

  type res =
    | Solution of Q.t Var_map.t
    | Unsatisfiable of cert

  let create param : t = {
    param: param;
    tab = Matrix.create ();
    basic = Vec.create ();
    nbasic = Vec.create ();
    assign = M.empty;
    bounds = M.empty;
    idx_basic = M.empty;
    idx_nbasic = M.empty;
  }

  let copy t = {
    param = Param.copy t.param;
    tab = Matrix.copy t.tab;
    basic = Vec.copy t.basic;
    nbasic = Vec.copy t.nbasic;
    assign = t.assign;
    bounds = t.bounds;
    idx_nbasic = t.idx_nbasic;
    idx_basic = t.idx_basic;
  }

  let index_basic (t:t) (x:basic_var) : int =
    match M.find x t.idx_basic with
      | n -> n
      | exception Not_found -> -1

  let index_nbasic (t:t) (x:nbasic_var) : int =
    match M.find x t.idx_nbasic with
      | n -> n
      | exception Not_found -> -1

  let[@inline] mem_basic (t:t) (x:var) : bool = M.mem x t.idx_basic
  let[@inline] mem_nbasic (t:t) (x:var) : bool = M.mem x t.idx_nbasic

  (* check invariants, for test purposes *)
  let check_invariants (t:t) : bool =
    Matrix.check_invariants t.tab &&
    Vec.for_all (fun v -> mem_basic t v) t.basic &&
    Vec.for_all (fun v -> mem_nbasic t v) t.nbasic &&
    Vec.for_all (fun v -> not (mem_nbasic t v)) t.basic &&
    Vec.for_all (fun v -> not (mem_basic t v)) t.nbasic &&
    Vec.for_all (fun v -> Var_map.mem v t.assign) t.nbasic &&
    Vec.for_all (fun v -> not (Var_map.mem v t.assign)) t.basic &&
    true

  (* find the definition of the basic variable [x],
     as a linear combination of non basic variables *)
  let find_expr_basic_opt t (x:var) : Q.t Vec.vector option =
    begin match index_basic t x with
      | -1 -> None
      | i -> Some (Matrix.get_row t.tab i)
    end

  let find_expr_basic t (x:basic_var) : Q.t Vec.vector =
    begin match find_expr_basic_opt t x with
      | None -> assert false
      | Some e -> e
    end

  (* build the expression [y = \sum_i (if x_i=y then 1 else 0)·x_i] *)
  let find_expr_nbasic t (x:nbasic_var) : Q.t Vec.vector =
    Vec.map
      (fun y -> if Var.compare x y = 0 then Q.one else Q.zero)
      t.nbasic

  (* TODO: avoid double lookup in maps *)
  (* find expression of [x] *)
  let find_expr_total (t:t) (x:var) : Q.t Vec.vector =
    if mem_basic t x then
      find_expr_basic t x
    else (
      assert (mem_nbasic t x);
      find_expr_nbasic t x
    )

  (* compute value of basic variable.
     It can be computed by using [x]'s definition
     in terms of nbasic variables, which have values *)
  let value_basic (t:t) (x:basic_var) : Erat.t =
    assert (mem_basic t x);
    let res = ref Erat.zero in
    let expr = find_expr_basic t x in
    for i = 0 to Vec.length expr - 1 do
      let val_nbasic_i =
        try M.find (Vec.get t.nbasic i) t.assign
        with Not_found -> assert false
      in
      res := Erat.sum !res (Erat.mul (Vec.get expr i) val_nbasic_i)
    done;
    !res

  (* extract a value for [x] *)
  let[@inline] value (t:t) (x:var) : Erat.t =
    try M.find x t.assign (* nbasic variables are assigned *)
    with Not_found -> value_basic t x

  (* trivial bounds *)
  let empty_bounds : Erat.t * Erat.t = Q.(Erat.make minus_inf zero, Erat.make inf zero)

  (* find bounds of [x] *)
  let[@inline] get_bounds (t:t) (x:var) : Erat.t * Erat.t =
    try M.find x t.bounds
    with Not_found -> empty_bounds

  (* is [value x] within the bounds for [x]? *)
  let is_within_bounds (t:t) (x:var) : bool * Erat.t =
    let v = value t x in
    let low, upp = get_bounds t x in
    if Erat.compare v low < 0 then
      false, low
    else if Erat.compare v upp > 0 then
      false, upp
    else
      true, v

  (* add nbasic variables *)
  let add_vars (t:t) (l:var list) : unit =
    (* add new variable to idx and array for nbasic, removing duplicates
       and variables already present *)
    let idx_nbasic, _, l =
      List.fold_left
        (fun ((idx_nbasic, offset, l) as acc) x ->
           if mem_basic t x then acc
           else if M.mem x idx_nbasic then acc
           else (
             (* allocate new index for [x] *)
             M.add x offset idx_nbasic, offset+1, x::l
           ))
        (t.idx_nbasic, Vec.length t.nbasic, [])
        l
    in
    (* add new columns to the matrix *)
    let old_dim = Matrix.n_col t.tab in
    List.iter (fun _ -> Matrix.push_col t.tab Q.zero) l;
    assert (old_dim + List.length l = Matrix.n_col t.tab);
    Vec.append_list t.nbasic (List.rev l);
    (* assign these variables *)
    t.assign <- List.fold_left (fun acc y -> M.add y Erat.zero acc) t.assign l;
    t.idx_nbasic <- idx_nbasic;
    ()

  (* define basic variable [x] by [eq] in [t] *)
  let add_eq (t:t) (x, eq : basic_var * _ list) : unit =
    if mem_basic t x || mem_nbasic t x then (
      invalid_arg (Format.sprintf "Variable `%a` already defined." Var.pp x);
    );
    add_vars t (List.map snd eq);
    (* add [x] as a basic var *)
    t.idx_basic <- M.add x (Vec.length t.basic) t.idx_basic;
    Vec.push t.basic x;
    (* add new row for defining [x] *)
    assert (Matrix.n_col t.tab > 0);
    Matrix.push_row t.tab Q.zero;
    let row_i = Matrix.n_row t.tab - 1 in
    assert (row_i >= 0);
    (* now put into the row the coefficients corresponding to [eq],
       expanding basic variables to their definition *)
    List.iter
      (fun (c, x) ->
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
  let add_bound_aux (t:t) (x:var) (low:Erat.t) (upp:Erat.t) : unit =
    add_vars t [x];
    let l, u = get_bounds t x in
    t.bounds <- M.add x (Erat.max l low, Erat.min u upp) t.bounds

  let add_bounds (t:t) ?strict_lower:(slow=false) ?strict_upper:(supp=false) (x, l, u) : unit =
    let e1 = if slow then Q.one else Q.zero in
    let e2 = if supp then Q.neg Q.one else Q.zero in
    add_bound_aux t x (Erat.make l e1) (Erat.make u e2);
    if mem_nbasic t x then (
      let b, v = is_within_bounds t x in
      if not b then (
        t.assign <- M.add x v t.assign;
      )
    )

  let add_lower_bound t ?strict x l = add_bounds t ?strict_lower:strict (x,l,Q.inf)
  let add_upper_bound t ?strict x u = add_bounds t ?strict_upper:strict (x,Q.minus_inf,u)

  (* full assignment *)
  let full_assign (t:t) : (var * Erat.t) Iter.t =
    Iter.append (Vec.to_iter t.nbasic) (Vec.to_iter t.basic)
    |> Iter.map (fun x -> x, value t x)

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
      M.fold
        (fun x ({base=low;eps_factor=e_low}, {base=upp;eps_factor=e_upp}) emax ->
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
        t.bounds
        Q.inf
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
    assert (mem_basic t x);
    let _, v = is_within_bounds t x in
    let b = Erat.compare (value t x) v < 0 in
    (* is nbasic var [y], with coeff [a] in definition of [x], suitable? *)
    let test (y:nbasic_var) (a:Q.t) : bool =
      assert (mem_nbasic t y);
      let v = value t y in
      let low, upp = get_bounds t y in
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
              if Var.compare y z <= 0
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
    (* swap values ([x] becomes assigned) *)
    let val_x = value t x in
    t.assign <- t.assign |> M.remove y |> M.add x val_x;
    (* Matrixrix Pivot operation *)
    let kx = index_basic t x in
    let ky = index_nbasic t y in
    for j = 0 to Vec.length t.nbasic - 1 do
      if Var.compare y (Vec.get t.nbasic j) = 0 then (
        Matrix.set t.tab kx j Q.(one / a)
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
    t.idx_basic <- t.idx_basic |> M.remove x |> M.add y kx;
    t.idx_nbasic <- t.idx_nbasic |> M.remove y |> M.add x ky;
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
    M.iter (fun x (l, u) -> if Erat.gt l u then raise (AbsurdBounds x)) t.bounds

  (* actual solving algorithm *)
  let solve_aux (t:t) : unit =
    check_bounds t;
    (* select the smallest basic variable that is not satisfied in the current
       assignment. *)
    let rec aux_select_basic_var () =
      match
        find_min_filter ~cmp:Var.compare
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
          t.assign <- M.add x v t.assign;
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
            (Vec.to_list t.nbasic)
        in
        Unsatisfiable { cert_var=x; cert_expr; cert_core=[]; } (* FIXME *)
      | AbsurdBounds x ->
        Unsatisfiable { cert_var=x; cert_expr=[]; cert_core=[]; }

  (* add [c·x] to [m] *)
  let add_expr_ (x:var) (c:Q.t) (m:Q.t M.t) =
    let c' = M.get_or ~default:Q.zero x m in
    let c' = Q.(c + c') in
    if Q.equal Q.zero c' then M.remove x m else M.add x c' m

  (* dereference basic variables from [c·x], and add the result to [m] *)
  let rec deref_var_ t x c m = match find_expr_basic_opt t x with
    | None -> add_expr_ x c m
    | Some expr_x ->
      let m = ref m in
      Vec.iteri
        (fun i c_i ->
           let y_i = Vec.get t.nbasic i in
           m := deref_var_ t y_i Q.(c * c_i) !m)
        expr_x;
      !m

  (* maybe invert bounds, if [c < 0] *)
  let scale_bounds c (l,u) : erat * erat =
    match Q.compare c Q.zero with
      | 0 -> Erat.zero, Erat.zero
      | n when n<0 -> Erat.mul c u, Erat.mul c l
      | _ -> Erat.mul c l, Erat.mul c u

  let check_cert (t:t) (c:cert) =
    let x = c.cert_var in
    let low_x, up_x = get_bounds t x in
    begin match c.cert_expr with
      | [] ->
        if Erat.compare low_x up_x > 0 then `Ok
        else `Bad_bounds (str_of_erat low_x, str_of_erat up_x)
      | expr ->
        let e0 = deref_var_ t x (Q.neg Q.one) M.empty in
        (* compute bounds for the expression [c.cert_expr],
           and also compute [c.cert_expr - x] to check if it's 0] *)
        let low, up, expr_minus_x =
          List.fold_left
            (fun (l,u,expr_minus_x) (c, y) ->
               let ly, uy = scale_bounds c (get_bounds t y) in
               assert (Erat.compare ly uy <= 0);
               let expr_minus_x = deref_var_ t y c expr_minus_x in
               Erat.sum l ly, Erat.sum u uy, expr_minus_x)
              (Erat.zero, Erat.zero, e0)
              expr
        in
        (* check that the expanded expression is [x], and that
           one of the bounds on [x] is incompatible with bounds of [c.cert_expr] *)
        if M.is_empty expr_minus_x then (
          if Erat.compare low_x up > 0 || Erat.compare up_x low < 0
          then `Ok
          else `Bad_bounds (str_of_erat low, str_of_erat up)
        ) else `Diff_not_0 expr_minus_x
    end

  (* printer *)

  let matrix_pp_width = ref 8

  let fmt_head = format_of_string "|%*s|| "
  let fmt_cell = format_of_string "%*s| "

  let pp_cert out (c:cert) = match c.cert_expr with
    | [] -> Format.fprintf out "(@[inconsistent-bounds %a@])" Var.pp c.cert_var
    | _ ->
      let pp_pair = Format.(hvbox ~i:2 @@ pair ~sep:(return "@ * ") Q.pp_print Var.pp) in
      Format.fprintf out "(@[<hv>cert@ :var %a@ :linexp %a@])"
        Var.pp c.cert_var
        Format.(within "[" "]" @@ hvbox @@ list ~sep:(return "@ + ") pp_pair)
        c.cert_expr

  let pp_mat out t =
    let open Format in
    fprintf out "@[<v>";
    (* header *)
    fprintf out fmt_head !matrix_pp_width "";
    Vec.iter (fun x -> fprintf out fmt_cell !matrix_pp_width (str_of_var x)) t.nbasic;
    fprintf out "@,";
    (* rows *)
    for i=0 to Matrix.n_row t.tab-1 do
      if i>0 then fprintf out "@,";
      let v = Vec.get t.basic i in
      fprintf out fmt_head !matrix_pp_width (str_of_var v);
      let row = Matrix.get_row t.tab i in
      Vec.iter (fun q -> fprintf out fmt_cell !matrix_pp_width (str_of_q q)) row;
    done;
    fprintf out "@]"

  let pp_assign =
    let open Format in
    let pp_pair =
      within "(" ")" @@ hvbox @@ pair ~sep:(return "@ := ") Var.pp Erat.pp
    in
    map Var_map.to_seq @@ within "(" ")" @@ hvbox @@ seq pp_pair

  let pp_bounds =
    let open Format in
    let pp_pairs out (x,(l,u)) =
      fprintf out "(@[%a =< %a =< %a@])" Erat.pp l Var.pp x Erat.pp u
    in
    map Var_map.to_seq @@ within "(" ")" @@ hvbox @@ seq pp_pairs

  let pp_full_state out (t:t) : unit =
    (* print main matrix *)
    Format.fprintf out
      "(@[<hv>simplex@ :n-row %d :n-col %d@ :mat %a@ :assign %a@ :bounds %a@])"
      (Matrix.n_row t.tab) (Matrix.n_col t.tab) pp_mat t pp_assign t.assign
      pp_bounds t.bounds
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
= struct
  include Make_inner(V)(L.Var_map)(V.Fresh)
  module L = L

  type op = Predicate.t = Leq | Geq | Lt | Gt | Eq | Neq

  type constr = L.Constr.t

  (* add a constraint *)
  let add_constr (t:t) (c:constr) : unit =
    let (x:var) = V.Fresh.fresh t.param in
    let e, op, q = L.Constr.split c in
    add_eq t (x, L.Comb.to_list e);
    begin match op with
      | Leq -> add_upper_bound t ~strict:false x q
      | Geq -> add_lower_bound t ~strict:false x q
      | Lt -> add_upper_bound t ~strict:true x q
      | Gt -> add_lower_bound t ~strict:true x q
      | Eq -> add_bounds t ~strict_lower:false ~strict_upper:false (x,q,q)
      | Neq -> assert false
    end
end

module Make_full(V : VAR_GEN)
  = Make_full_for_expr(V)(Linear_expr.Make(struct include Q let pp = pp_print end)(V))
