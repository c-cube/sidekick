
(** {1 Fast Simplex for CDCL(T)}

    We follow the paper "Integrating Simplex with DPLL(T )" from
    de Moura and Dutertre.
*)

module type VAR = Linear_expr_intf.VAR

(** {2 Basic operator} *)
module Op = struct
  type t =
    | Leq
    | Lt
    | Geq
    | Gt

  let to_string = function
    | Leq -> "<="
    | Lt -> "<"
    | Geq -> ">="
    | Gt -> ">"
  let pp out op = Fmt.string out (to_string op)
end

module type S = sig
  module V : VAR
  module V_map : CCMap.S with type key = V.t

  type num = Q.t (** Numbers *)

  module Constraint : sig
    type op = Op.t

    (** A constraint is the comparison of a variable to a constant. *)
    type t = private {
      op: op;
      lhs: V.t;
      rhs: num;
    }

    val leq : V.t -> num -> t
    val lt : V.t -> num -> t
    val geq : V.t -> num -> t
    val gt : V.t -> num -> t

    val pp : t Fmt.printer
  end

  module Subst : sig
    type t = num V_map.t
    val pp : t Fmt.printer
    val to_string : t -> string
  end

  type t

  val create : unit -> t
  (** Create a new simplex. *)

  val push_level : t -> unit

  val pop_levels : t -> int -> unit

  val define : t -> V.t -> (num * V.t) list -> unit
  (** Define a basic variable in terms of other variables.
      This is useful to "name" a linear expression and get back a variable
      that can be used in a {!Constraint.t} *)

  type unsat_cert = {
    cert_bounds: (num * V.lit) list;
    cert_defs: (V.t * (num * V.t) list) list; (* definitions used *)
  }

  module Unsat_cert : sig
    type t = unsat_cert
    val pp : t Fmt.printer
  end

  exception E_unsat of Unsat_cert.t

  val add_constraint : t -> Constraint.t -> V.lit -> unit
  (** Add a constraint to the simplex.
      @raise Unsat if it's immediately obvious that this is not satisfiable. *)

  val check_exn : t -> unit
  (** Check the whole simplex for satisfiability.
      @raise Unsat if the constraints are not satisfiable. *)

  type result =
    | Sat of Subst.t
    | Unsat of Unsat_cert.t

  val check : t -> result
  (** Call {!check_exn} and return a model or a proof of unsat. *)
end

(* TODO(optim): page 14, paragraph 2: we could detect which variables occur in no
   atom after preprocessing; then these variables can be "inlined" (removed
   by Gaussian elimination) as a preprocessing step, and this removes one column
   and maybe one row if it was basic. *)

module Make(Var: VAR)
  : S with module V = Var
= struct
  module V = Var
  module V_map = CCMap.Make(Var)

  type num = Q.t (** Numbers *)

  module Constraint = struct
    type op = Op.t

    (** A constraint is the comparison of a variable to a constant. *)
    type t = {
      op: op;
      lhs: V.t;
      rhs: num;
    }

    let pp out (self:t) =
      Fmt.fprintf out "(@[%a %s@ %a@])" V.pp self.lhs
        (Op.to_string self.op) Q.pp_print self.rhs

    let leq lhs rhs = {lhs;rhs;op=Op.Leq}
    let lt lhs rhs = {lhs;rhs;op=Op.Lt}
    let geq lhs rhs = {lhs;rhs;op=Op.Geq}
    let gt lhs rhs = {lhs;rhs;op=Op.Gt}
  end

  module Subst = struct
    type t = num V_map.t
    let pp out (self:t) : unit =
      let pp_pair out (v,n) =
        Fmt.fprintf out "(@[%a := %a@])" V.pp v Q.pp_print n in
      Fmt.fprintf out "{@[%a@]}" (Fmt.iter pp_pair) (V_map.to_iter self)
    let to_string = Fmt.to_string pp
  end

  (** An extended rational, used to introduce ε so we can use strict
      comparisons in an algorithm designed to handle >= only.

      In a way, an extended rational is a tuple `(base, factor)`
      ordered lexicographically. *)
  type erat = {
    base: num; (** reference number *)
    eps_factor: num; (** coefficient for epsilon, the infinitesimal *)
  }

  (** {2 Epsilon-rationals, used for strict bounds} *)
  module Erat = struct
    type t = erat

    let zero : t = {base=Q.zero; eps_factor=Q.zero}

    let[@inline] make base eps_factor : t = {base; eps_factor}
    let[@inline] make_q x = make x Q.zero
    let[@inline] base t = t.base
    let[@inline] eps_factor t = t.eps_factor
    let[@inline] ( * ) k e = make Q.(k * e.base) Q.(k * e.eps_factor)
    let[@inline] ( / ) e k = make Q.(e.base / k) Q.(e.eps_factor / k)
    let[@inline] (+) e1 e2 = make Q.(e1.base + e2.base) Q.(e1.eps_factor + e2.eps_factor)
    let[@inline] (-) e1 e2 = make Q.(e1.base - e2.base) Q.(e1.eps_factor - e2.eps_factor)
    let[@inline] compare e1 e2 = match Q.compare e1.base e2.base with
      | 0 -> Q.compare e1.eps_factor e2.eps_factor
      | x -> x

    let[@inline] (<) a b = compare a b < 0
    let[@inline] (<=) a b = compare a b <= 0
    let[@inline] (>) a b = compare a b > 0
    let[@inline] (>=) a b = compare a b >= 0

    let[@inline] min x y = if x <= y then x else y
    let[@inline] max x y = if x >= y then x else y

    let[@inline] evaluate (epsilon:Q.t) (e:t) : Q.t = Q.(e.base + epsilon * e.eps_factor)

    let pp out e : unit =
      if Q.equal Q.zero (eps_factor e)
      then Q.pp_print out (base e)
      else
        Fmt.fprintf out "(@[<h>%a + @<1>ε * %a@])"
          Q.pp_print (base e) Q.pp_print (eps_factor e)
  end

  type var_idx = int

  (** {2 Matrix}
    The matrix [A] from the paper, with m rows and n columns.
    - m is the number of basic variables (defined in terms of non-basic variables)
    - n is the total number of variables, basic and non-basic.

    The invariant that the simplex maintains at all times is that [Ax = 0],
    where [x] is the vector of values of all variables (basic and non-basic).
  *)

  module Matrix : sig
    type t

    val create : unit -> t

    val pp : t Fmt.printer
    val to_string : t -> string

    val n_rows : t -> int
    val n_cols : t -> int

    val add_column : t -> unit
    (** Add a non-basic variable (only adds a column) *)

    val add_row_and_column : t -> int
    (** Add a basic variable. returns the row index. *)

    val get_row_var_idx : t -> int -> var_idx
    (** Index of the basic variable for row [i] *)

    val set_row_var_idx : t -> int -> var_idx -> unit
    (** Set index of the basic variable for row [i] *)

    val get : t -> int -> int -> num

    val set : t -> int -> int -> num -> unit

    val add : t -> int -> int -> num -> unit

    val mult : t -> int -> int -> num -> unit
  end = struct
    type row = {
      mutable var_idx: var_idx;
      cols: num Vec.t;
    }
    type t = {
      rows: row Vec.t
    }

    let create() : t = {rows=Vec.create()}

    let[@inline] n_rows self = Vec.size self.rows
    let n_cols self =
      if n_rows self=0 then 0
      else Vec.size (Vec.get self.rows 0).cols

    let pp out self =
      Fmt.fprintf out "{@[<v>";
      Vec.iteri (fun i row ->
          Fmt.fprintf out "@[<hov2>%-5d: %a@]@," i
            (Fmt.iter ~sep:(Fmt.return "@ ") Q.pp_print) (Vec.to_seq row.cols))
        self.rows;
      Fmt.fprintf out "@]}"
    let to_string = Fmt.to_string pp

    let add_column self =
      Vec.iter (fun r -> Vec.push r.cols Q.zero) self.rows

    let add_row_and_column self : int =
      let n = n_rows self in
      let j = n_cols self in
      add_column self;
      let row = {var_idx=j; cols=Vec.make (j+1) Q.zero} in
      Vec.push self.rows row;
      n

    let[@inline] get_row_var_idx self i = (Vec.get self.rows i).var_idx
    let[@inline] set_row_var_idx self i n = (Vec.get self.rows i).var_idx <- n

    let[@inline] get self i j : num = Vec.get (Vec.get self.rows i).cols j

    let[@inline] set self i j n : unit =
      let r = Vec.get self.rows i in
      Vec.set r.cols j n

    (* add [n] to [m_ij] *)
    let add self i j n : unit =
      let r = Vec.get self.rows i in
      Vec.set r.cols j Q.(Vec.get r.cols j + n)

    (* multiply [m_ij] by [c] *)
    let mult self i j c : unit =
      let r = Vec.get self.rows i in
      let n_j = Vec.get r.cols j in
      if Q.sign n_j <> 0 then (
        Vec.set r.cols j Q.(n_j * c)
      )
  end

  type bound = {
    b_val: erat;
    b_lit: Var.lit;
  }

  type var_state = {
    var: V.t;
    mutable value: erat;
    idx: int; (* index in {!t.vars} *)
    mutable basic_idx: int; (* index of the row in the matrix, if any. -1 otherwise *)
    mutable l_bound: bound option;
    mutable u_bound: bound option;
  }

  module Var_state = struct
    type t = var_state

    let[@inline] is_basic (self:t) : bool = self.basic_idx >= 0
    let[@inline] is_n_basic (self:t) : bool = self.basic_idx < 0
    let pp out self =
      Fmt.fprintf out "(@[var %a@ :basic %B@ :value %a@ :lbound %a@ :ubound %a@])"
        Var.pp self.var (is_basic self) Erat.pp self.value
        Fmt.(Dump.option (map (fun b->b.b_val) Erat.pp)) self.l_bound
        Fmt.(Dump.option (map (fun b->b.b_val) Erat.pp)) self.u_bound
  end

  type t = {
    matrix: Matrix.t;
    vars: var_state Vec.t; (* index -> var with this index *)
    mutable var_tbl: var_state V_map.t; (* var -> its state *)
    bound_stack: (var_state * [`Upper|`Lower] * bound option) Backtrack_stack.t;
  }

  let push_level self : unit =
    Backtrack_stack.push_level self.bound_stack

  let pop_levels self n : unit =
    Backtrack_stack.pop_levels self.bound_stack n
      ~f:(fun (var, kind, bnd) ->
          match kind with
          | `Upper -> var.u_bound <- bnd
          | `Lower -> var.l_bound <- bnd);
    ()

  let pp out (self:t) : unit =
    Fmt.fprintf out "(@[simplex@ :vars %a@ :matrix %a@])"
      (Vec.pp Var_state.pp) self.vars
      Matrix.pp self.matrix

  let[@inline] has_var_ (self:t) x : bool = V_map.mem x self.var_tbl
  let[@inline] find_var_ (self:t) x : var_state =
    try V_map.find x self.var_tbl
    with Not_found -> Error.errorf "variable is not in the simplex" Var.pp x

  let define (self:t) (x:V.t) (le:_ list) : unit =
    assert (not (has_var_ self x));
    Log.debugf 5 (fun k->k "(@[simplex.define@ %a@ :le %a@])"
                     Var.pp x Fmt.(Dump.(list @@ pair Q.pp_print Var.pp)) le);
    let n = Matrix.add_row_and_column self.matrix in
    let vs = {
      var=x; value=Erat.zero;
      idx=Vec.size self.vars;
      basic_idx=n;
      l_bound=None;
      u_bound=None;
    } in
    Vec.push self.vars vs;
    self.var_tbl <- V_map.add x vs self.var_tbl;
    (* set coefficients in the matrix's new row: [-x + le = 0] *)
    Matrix.set self.matrix n vs.idx Q.minus_one;
    List.iter
      (fun (coeff,v2) ->
         let vs2 = find_var_ self v2 in
         Matrix.add self.matrix n vs2.idx coeff;
      ) le;
    ()

  (* find the state for [x], or add [x] as a non-basic variable *)
  let find_or_create_n_basic_var_ (self:t) (x:V.t) : var_state =
    try V_map.find x self.var_tbl
    with Not_found ->
      Matrix.add_column self.matrix;
      let vs = {
        idx=Vec.size self.vars;
        basic_idx= -1;
        var=x;
        l_bound=None;
        u_bound=None;
        value=Erat.zero;
      } in
      assert (Var_state.is_n_basic vs);
      self.var_tbl <- V_map.add x vs self.var_tbl;
      Vec.push self.vars vs;
      vs

  (* update the simplex so that non-basic [x] is now assigned value [n].
     See page 14, figure 3.1.
  *)
  let update_n_basic (self:t) (x:var_state) (v:erat) : unit =
    assert (Var_state.is_n_basic x);
    let m = self.matrix in
    let i = x.idx in

    let diff = Erat.(v - x.value) in

    for j=0 to Matrix.n_rows m - 1 do
      let a_ji = Matrix.get m j i in
      let x_j = Vec.get self.vars (Matrix.get_row_var_idx m j) in
      assert (Var_state.is_basic x_j);
      (* value of [x_j] by [a_ji * diff] *)
      x_j.value <- Erat.(x_j.value + a_ji * diff);
    done;
    x.value <- v;
    ()

  (* pivot [x_i] (basic) and [x_j] (non-basic), setting value of [x_i]
     to [v] at the same time.
     See page 14, figure 3.1 *)
  let pivot_and_update (self:t) (x_i:var_state) (x_j:var_state) (v:erat) : unit =
    assert (Var_state.is_basic x_i);
    assert (Var_state.is_n_basic x_j);
    let m = self.matrix in
    let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
    assert (Q.sign a_ij <> 0);
    let theta = Erat.((v - x_i.value) / a_ij) in
    x_i.value <- v;
    x_j.value <- Erat.(x_j.value + theta);

    for k=0 to Matrix.n_rows m-1 do
      if k <> x_i.basic_idx then (
        let x_k = Vec.get self.vars (Matrix.get_row_var_idx m k) in
        let a_kj = Matrix.get m x_k.basic_idx x_j.idx in
        x_k.value <- Erat.(x_k.value + a_kj * theta);
      )
    done;

    (* now pivot the variables so that [x_j]'s coeff is -1 *)
    let new_coeff = Q.(minus_one / a_ij) in
    for k=0 to Matrix.n_cols m-1 do
      Matrix.mult m x_i.idx k new_coeff;
    done;
    x_j.basic_idx <- x_i.basic_idx;
    x_i.basic_idx <- -1;
    Matrix.set_row_var_idx m x_j.basic_idx x_j.idx;

    assert (Var_state.is_basic x_j);
    assert (Var_state.is_n_basic x_i);

    ()

  type unsat_cert = {
    cert_bounds: (num * V.lit) list;
    cert_defs: (V.t * (num * V.t) list) list; (* definitions used *)
  }

  module Unsat_cert = struct
    type t = unsat_cert

    let pp out (self:t) =
      let pp_bnd out (n,lit) =
        Fmt.fprintf out "(@[%a@ coeff %a@])" V.pp_lit lit Q.pp_print n
      in
      Fmt.fprintf out "(@[cert@ :bounds %a@ :defs %a@])"
        Fmt.(Dump.list pp_bnd) self.cert_bounds
        Fmt.(Dump.list (Dump.pair V.pp (Dump.list (Dump.pair Q.pp_print V.pp)))) self.cert_defs

    let mk ~defs ~bounds : t =
      { cert_defs=defs; cert_bounds=bounds }
  end

  exception E_unsat of Unsat_cert.t

  let add_constraint (self:t) (c:Constraint.t) (lit:V.lit) : unit =
    let open Constraint in
    let vs = find_or_create_n_basic_var_ self c.lhs in
    let is_lower_bnd, new_bnd_val =
      match c.op with
      | Leq -> false, Erat.make_q c.rhs
      | Lt -> false, Erat.make c.rhs Q.minus_one
      | Geq -> true, Erat.make_q c.rhs
      | Gt -> true, Erat.make c.rhs Q.one
    in
    let new_bnd = {b_val=new_bnd_val; b_lit=lit} in
    if is_lower_bnd then (
      begin match vs.l_bound, vs.u_bound with
        | _, Some upper when Erat.(new_bnd.b_val > upper.b_val) ->
          (* [b_val <= x <= upper], but [b_val > upper] *)
          let cert = Unsat_cert.mk ~defs:[]
              ~bounds:[(Q.one, upper.b_lit); (Q.one, lit)] in
          raise (E_unsat cert)
        | Some lower, _ when Erat.(lower.b_val >= new_bnd.b_val) ->
          () (* subsumed by existing constraint, do nothing *)
        | _ ->
          (* save current bound *)
          Backtrack_stack.push self.bound_stack (vs, `Lower, vs.l_bound);
          vs.l_bound <- Some new_bnd;

          if Var_state.is_n_basic vs &&
             Erat.(vs.value < new_bnd.b_val) then (
            (* line 5: need to update non-basic variable *)
            update_n_basic self vs new_bnd.b_val
          )
      end
    ) else (
      begin match vs.l_bound, vs.u_bound with
        | Some lower, _ when Erat.(new_bnd.b_val < lower.b_val) ->
          (* [lower <= x <= b_val], but [b_val < lower] *)
          let cert = Unsat_cert.mk ~defs:[]
              ~bounds:[(Q.one, lower.b_lit); (Q.one, lit)] in
          raise (E_unsat cert)
        | _, Some upper when Erat.(upper.b_val <= new_bnd.b_val) ->
          () (* subsumed *)
        | _ ->
          Backtrack_stack.push self.bound_stack (vs, `Upper, vs.u_bound);
          vs.u_bound <- Some new_bnd;

          if Var_state.is_n_basic vs &&
             Erat.(vs.value > new_bnd.b_val) then (
            (* line 5: need to update non-basic variable *)
            update_n_basic self vs new_bnd.b_val
          )
      end
    )

  (* try to find basic variable that doesn't respect one of its bounds *)
  let find_basic_var_ (self:t) : (var_state * [`Lower | `Upper] * bound) option =
    let n = Matrix.n_rows self.matrix in
    let rec aux i =
      if i >= n then None
      else (
        let x_i = Vec.get self.vars (Matrix.get_row_var_idx self.matrix i) in
        let v_i = x_i.value in
        match x_i.l_bound, x_i.u_bound with
        | Some l, _ when Erat.(l.b_val > v_i) -> Some (x_i, `Lower, l)
        | _, Some u when Erat.(u.b_val < v_i) -> Some (x_i, `Upper, u)
        | _ -> (aux[@tailcall]) (i+1)
      )
    in
    aux 0

  let find_n_basic_var_ (self:t) ~f : var_state option =
    let rec aux j =
      if j >= Vec.size self.vars then None
      else (
        let x_j = Vec.get self.vars j in
        if Var_state.is_n_basic x_j && f x_j then Some x_j
        else aux (j+1)
      )
    in
    aux 0

  (* true if [x.value < x.u_bound] *)
  let has_upper_slack (x:var_state) : bool =
    match x.u_bound with
    | None -> true
    | Some bnd -> Erat.(x.value < bnd.b_val)

  (* true if [x.value > x.l_bound] *)
  let has_lower_slack (x:var_state) : bool =
    match x.l_bound with
    | None -> true
    | Some bnd -> Erat.(x.value > bnd.b_val)

  (* make a certificate from the row of basic variable [x_i] which is outside
     one of its bound, and whose row is tight on all non-basic variables *)
  let cert_of_row_ (self:t) (x_i:var_state) ~is_lower : unsat_cert =
    Log.debugf 50 (fun k->k "(@[simplex.cert-of-row[lower: %B]@ x_i=%a@ %a@])"
                      is_lower Var_state.pp x_i pp self);
    assert (Var_state.is_basic x_i);
    (* TODO: store initial definition for each matrix row *)
    let defs = [] in
    let bounds = [] in (* TODO: use all bounds in the row *)
    Unsat_cert.mk ~defs ~bounds

  (* main satisfiability check.
     page 15, figure 3.2 *)
  let check_exn (self:t) : unit =
    let exception Stop in
    Log.debugf 5 (fun k->k "(@[simplex2.check@ %a@])" Matrix.pp self.matrix);

    let m = self.matrix in
    try
      while true do
        Log.debugf 50 (fun k->k "(@[simplex2.check.iter@ %a@])" Matrix.pp self.matrix);

        (* basic variable that doesn't respect its bound *)
        let x_i, is_lower, bnd = match find_basic_var_ self with
          | Some (x, `Lower, bnd) -> x, true, bnd
          | Some (x, `Upper, bnd) -> x, false, bnd
          | None -> raise_notrace Stop (* line 4: we are done *)
        in

        if is_lower then (
          (* line 5 *)
          let x_j =
            match
              find_n_basic_var_ self
                ~f:(fun x_j ->
                    let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
                    (Q.sign a_ij > 0 && has_upper_slack x_j) ||
                    (Q.sign a_ij < 0 && has_lower_slack x_j))
            with
            | Some x -> x
            | None ->
              let cert = cert_of_row_ self x_i ~is_lower:true in
              raise (E_unsat cert)
          in
          assert (Var_state.is_n_basic x_j);

          (* line 9 *)
          pivot_and_update self x_i x_j bnd.b_val
        ) else (
          (* line 10 *)
          let x_j =
            match
              find_n_basic_var_ self
                ~f:(fun x_j ->
                    let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
                    (Q.sign a_ij < 0 && has_upper_slack x_j) ||
                    (Q.sign a_ij > 0 && has_lower_slack x_j))
            with
            | Some x -> x
            | None ->
              let cert = cert_of_row_ self x_i ~is_lower:false in
              raise (E_unsat cert)
          in
          assert (Var_state.is_n_basic x_j);

          (* line 14 *)
          pivot_and_update self x_i x_j bnd.b_val
        )
      done;
    with Stop -> ()

  let create () : t =
    let self = {
      matrix=Matrix.create();
      vars=Vec.create();
      var_tbl=V_map.empty;
      bound_stack=Backtrack_stack.create();
    } in
    self

  type result =
    | Sat of Subst.t
    | Unsat of unsat_cert

  (* Find an epsilon that is small enough for finding a solution, yet
     it must be positive.

     {!Erat.t} values are used to turn strict bounds ([X > 0]) into
     non-strict bounds ([X >= 0 + ε]), because the simplex algorithm
     only deals with non-strict bounds.
     When a solution is found, we need to turn {!Erat.t} into {!Q.t} by
     finding a rational value that is small enough that it will fit into
     all the intervals of [t]. This rational will be the actual value of [ε].
  *)
  let solve_epsilon (self:t) : Q.t =
    let emax =
      Iter.fold
        (fun emax x ->
           let {base=v; eps_factor=e_v} = x.value in
           (* lower bound *)
           let emax = match x.l_bound with
             | Some {b_val={base=low;eps_factor=e_low};_} when Q.(e_v < e_low) ->
               Q.min emax Q.((low - v) / (e_v - e_low))
             | _ -> emax
           in
           (* upper bound *)
           let emax = match x.u_bound with
             | Some { b_val={base=upp;eps_factor=e_upp}; _} when Q.(e_v > e_upp) ->
               min emax Q.((upp - v) / (e_v - e_upp))
             | _ -> emax
           in
           emax)
        Q.inf (Vec.to_seq self.vars)
    in
    if Q.compare emax Q.one >= 0 then Q.one else emax

  let model_ self =
    let eps = solve_epsilon self in
    let subst =
      Vec.to_seq self.vars
      |> Iter.fold
        (fun subst x ->
           let {base;eps_factor} = x.value in
           let v = Q.(base + eps * eps_factor) in
           V_map.add x.var v subst)
        V_map.empty
    in
    subst

  let check (self:t) : result =
    try
      check_exn self;
      let m = model_ self in
      Sat m
    with E_unsat c -> Unsat c

  (* TODO

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
     *)
end
