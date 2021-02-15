
(** {1 Fast Simplex for CDCL(T)}

    We follow the paper "Integrating Simplex with DPLL(T )" from
    de Moura and Dutertre.
*)

open CCMonomorphic

module type VAR = Linear_expr_intf.VAR

(** {2 Basic operator} *)
module Op = struct
  type t =
    | Leq
    | Lt
    | Geq
    | Gt

  let neg_sign = function
    | Leq -> Geq
    | Lt -> Gt
    | Geq -> Leq
    | Gt -> Lt

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
    type t = {
      op: op;
      lhs: V.t;
      rhs: num;
    }

    val mk : V.t -> op -> num -> t
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

  type unsat_cert

  module Unsat_cert : sig
    type t = unsat_cert
    val lits : t -> V.lit list (* unsat core *)
    val pp : t Fmt.printer
  end

  exception E_unsat of Unsat_cert.t

  val add_var : t -> V.t -> unit
  (** Make sure the variable exists in the simplex. *)

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

  (**/**)
  val _check_invariants : t -> unit
  (* check internal invariants *)
  (**/**)
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

  let pp_q_float n out q = Fmt.fprintf out "%*.1f" n (Q.to_float q)
  let pp_q_dbg = pp_q_float 1

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
        (Op.to_string self.op) pp_q_dbg self.rhs

    let mk lhs op rhs : t = {lhs;op;rhs}
    let leq lhs rhs = {lhs;rhs;op=Op.Leq}
    let lt lhs rhs = {lhs;rhs;op=Op.Lt}
    let geq lhs rhs = {lhs;rhs;op=Op.Geq}
    let gt lhs rhs = {lhs;rhs;op=Op.Gt}
  end

  module Subst = struct
    type t = num V_map.t
    let pp out (self:t) : unit =
      let pp_pair out (v,n) =
        Fmt.fprintf out "(@[%a := %a@])" V.pp v pp_q_dbg n in
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
    let[@inline] (=) a b = compare a b = 0

    let[@inline] min x y = if x <= y then x else y
    let[@inline] max x y = if x >= y then x else y

    let[@inline] evaluate (epsilon:Q.t) (e:t) : Q.t = Q.(e.base + epsilon * e.eps_factor)

    let pp out e : unit =
      if Q.equal Q.zero (eps_factor e)
      then pp_q_dbg out (base e)
      else
        Fmt.fprintf out "(@[<h>%a + @<1>ε * %a@])"
          pp_q_dbg (base e) pp_q_dbg (eps_factor e)
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

    val add_row_and_column : t -> f:(row_idx:int -> col_idx:int -> var_state) -> var_state
    (** Add a basic variable. *)

    val get_row_var : t -> int -> var_state
    (** The basic variable for row [i] *)

    val set_row_var : t -> int -> var_state -> unit
    (** Set basic variable for row [i] *)

    val get : t -> int -> int -> num

    val set : t -> int -> int -> num -> unit

    val add : t -> int -> int -> num -> unit

    val mult : t -> int -> int -> num -> unit
  end = struct
    type row = {
      mutable vs: var_state;
      cols: num Vec.t;
    }
    type t = {
      mutable n_cols: int;
      rows: row Vec.t
    }

    let create() : t =
      {n_cols=0; rows=Vec.create()}

    let[@inline] n_rows self = Vec.size self.rows
    let[@inline] n_cols self = self.n_cols

    let pp out self =
      Fmt.fprintf out "@[<v1>{matrix[%dx%d]@," (n_rows self) (n_cols self);

      (* header *)
      let ppi out i =
        Fmt.string out @@ CCString.pad ~side:`Left 6 @@ Printf.sprintf "v%d" i in
      Fmt.fprintf out "{@[<hov2>%9s: %a@]}" "vars"
        (Fmt.iter ~sep:(Fmt.return "@ ") ppi) CCInt.(0 -- (n_cols self-1));

      Vec.iteri (fun i row ->
          let hd =
            CCString.pad ~side:`Left 6 @@
            Printf.sprintf "r%d (v%d)" i row.vs.idx in
          Fmt.fprintf out "@,{@[<hov2>%9s: %a@]}" hd
            (Fmt.iter ~sep:(Fmt.return "@ ") (pp_q_float 6)) (Vec.to_seq row.cols))
        self.rows;
      Fmt.fprintf out "@;<0 -1>}@]"
    let to_string = Fmt.to_string pp

    let add_column self =
      self.n_cols <- 1 + self.n_cols;
      Vec.iter (fun r -> Vec.push r.cols Q.zero) self.rows

    let add_row_and_column self ~f : var_state =
      let n = n_rows self in
      let j = n_cols self in
      add_column self;
      let cols = Vec.make (j+1) Q.zero in
      for _k=0 to j do Vec.push cols Q.zero done;
      let vs = f ~row_idx:n ~col_idx:j in
      let row = {vs; cols} in
      Vec.push self.rows row;
      vs

    let[@inline] get_row_var self i = (Vec.get self.rows i).vs
    let[@inline] set_row_var self i v = (Vec.get self.rows i).vs <- v

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
      if Q.(n_j <> zero) then (
        Vec.set r.cols j Q.(n_j * c)
      )
  end

  module Var_state = struct
    type t = var_state
    let (==) : t -> t -> bool = Containers.Stdlib.(==)
    let (!=) : t -> t -> bool = Containers.Stdlib.(!=)

    let[@inline] is_basic (self:t) : bool = self.basic_idx >= 0
    let[@inline] is_n_basic (self:t) : bool = self.basic_idx < 0

    let in_bounds_ self =
      (match self.l_bound with None -> true | Some b -> Erat.(self.value >= b.b_val)) &&
      (match self.u_bound with None -> true | Some b -> Erat.(self.value <= b.b_val))

    let pp_name out self = Fmt.fprintf out "v%d" self.idx
    let pp out self =
      let bnd_status = if in_bounds_ self then "" else "(oob)" in
      let pp_bnd what out = function
        | None -> ()
        | Some b -> Fmt.fprintf out "@ @[%s %a@]" what Erat.pp b.b_val
      and pp_basic_idx out () =
        if self.basic_idx < 0 then () else Fmt.int out self.basic_idx
      in
      Fmt.fprintf out
        "(@[v%d[%s%a]%s@ :value %a%a%a@])"
        self.idx (if is_basic self then "B" else "N") pp_basic_idx ()
        bnd_status Erat.pp self.value
        (pp_bnd ":lower") self.l_bound (pp_bnd ":upper") self.u_bound
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

  let pp_stats out (self:t) : unit =
    Fmt.fprintf out "(@[simplex@ :n-vars %d@ :n-rows %d@])"
      (Vec.size self.vars) (Matrix.n_rows self.matrix)

  let pp out (self:t) : unit =
    Fmt.fprintf out "(@[simplex@ @[<1>:vars@ [@[<hov>%a@]]@]@ @[<1>:matrix@ %a@]@])"
      (Vec.pp Var_state.pp) self.vars
      Matrix.pp self.matrix

  (* for debug purposes *)
  let _check_invariants self : unit =
    Vec.iteri (fun i v -> assert(v.idx = i)) self.vars;
    let n = Vec.size self.vars in
    assert (Matrix.n_rows self.matrix = 0 || Matrix.n_cols self.matrix = n);
    for i = 0 to Matrix.n_rows self.matrix-1 do
      let v = Matrix.get_row_var self.matrix i in
      assert (Var_state.is_basic v);
      assert (v.basic_idx = i);
      assert Q.(Matrix.get self.matrix v.basic_idx v.idx = minus_one);

      (* basic vars are only defined in terms of non-basic vars *)
      Vec.iteri
        (fun j v_j ->
           if Var_state.(v != v_j) && Q.(Matrix.get self.matrix i j <> zero) then (
             assert (Var_state.is_n_basic v_j)
           ))
        self.vars;

      (* sum of each row must be 0 *)
      let sum =
        Vec.fold
          (fun sum v ->
             Erat.(sum + Matrix.get self.matrix i v.idx * v.value))
          Erat.zero self.vars
      in
      Log.debugf 50 (fun k->k "row %d: sum %a" i Erat.pp sum);
      assert Erat.(sum = zero);

    done;
    ()

  (* for internal checking *)
  let[@inline] _check_invariants_internal self =
    if false (* FUDGE *) then _check_invariants self

  let[@inline] has_var_ (self:t) x : bool = V_map.mem x self.var_tbl
  let[@inline] find_var_ (self:t) x : var_state =
    try V_map.find x self.var_tbl
    with Not_found -> Error.errorf "variable is not in the simplex" Var.pp x

  (* define [x] as a basic variable *)
  let define (self:t) (x:V.t) (le:_ list) : unit =
    assert (not (has_var_ self x));
    (* Log.debugf 50 (fun k->k "define-in: %a" pp self); *)
    let le = List.map (fun (q,v) -> q, find_var_ self v) le in

    (* initial value for the new variable *)
    let value =
      List.fold_left
        (fun sum (c,v) -> Erat.(sum + c * v.value)) Erat.zero le
    in

    let vs =
      Matrix.add_row_and_column self.matrix
        ~f:(fun ~row_idx ~col_idx ->
            {
              var=x; value;
              idx=col_idx;
              basic_idx=row_idx;
              l_bound=None;
              u_bound=None;
            })
    in
    Log.debugf 5 (fun k->k "(@[simplex.define@ @[v%d :var %a@]@ :linexpr %a@])"
                     vs.idx Var.pp x Fmt.(Dump.(list @@ pair pp_q_dbg Var_state.pp_name)) le);

    assert (Var_state.is_basic vs);
    assert Var_state.(Matrix.get_row_var self.matrix vs.basic_idx == vs);
    Vec.push self.vars vs;
    self.var_tbl <- V_map.add x vs self.var_tbl;

    (* set coefficients in the matrix's new row: [-x + le = 0] *)
    Matrix.set self.matrix vs.basic_idx vs.idx Q.minus_one;
    List.iter
      (fun (coeff,v2) ->
         assert Containers.Stdlib.(v2 != vs);

         if Var_state.is_basic v2 then (
           (* [v2] is also basic, so instead of depending on it,
              we depend on its definition in terms of non-basic variables. *)

           for k=0 to Matrix.n_cols self.matrix - 1 do
             if k <> v2.idx then (
               let v2_jk = Matrix.get self.matrix v2.basic_idx k in
               if Q.(v2_jk <> zero) then (
                 let v_k = Vec.get self.vars k in
                 assert (Var_state.is_n_basic v_k);

                 (* [v2 := v2_jk * v_k + …], so [v := … + coeff * v2_jk * v_k] *)
                 Matrix.add self.matrix vs.basic_idx k Q.(coeff * v2_jk);
               );
             );
           done;
         ) else (
           (* directly add coefficient with non-basic var [v2] *)
           Matrix.add self.matrix vs.basic_idx v2.idx coeff;
         );
      ) le;

    (* Log.debugf 50 (fun k->k "post-define: %a" pp self); *)
    _check_invariants_internal self;
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
    Log.debugf 50
      (fun k->k "(@[<hv>simplex.update-n-basic@ %a@ :new-val %a@])"
          Var_state.pp x Erat.pp v);
    _check_invariants_internal self;

    let m = self.matrix in
    let i = x.idx in

    let diff = Erat.(v - x.value) in

    for j=0 to Matrix.n_rows m - 1 do
      let a_ji = Matrix.get m j i in
      let x_j = Matrix.get_row_var m j in
      assert (Var_state.is_basic x_j);
      (* value of [x_j] by [a_ji * diff] *)
      let new_val = Erat.(x_j.value + a_ji * diff) in
      Log.debugf 50 (fun k->k "new-val %a@ := %a" Var_state.pp x_j Erat.pp new_val);
      x_j.value <- new_val;
    done;
    x.value <- v;
    _check_invariants_internal self;
    ()

  (* pivot [x_i] (basic) and [x_j] (non-basic), setting value of [x_i]
     to [v] at the same time.
     See page 14, figure 3.1 *)
  let pivot_and_update (self:t) (x_i:var_state) (x_j:var_state) (v:erat) : unit =
    assert (Var_state.is_basic x_i);
    assert (Var_state.is_n_basic x_j);
    _check_invariants_internal self;

    let m = self.matrix in
    let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
    assert (Q.sign a_ij <> 0);
    let theta = Erat.((v - x_i.value) / a_ij) in
    x_i.value <- v;
    x_j.value <- Erat.(x_j.value + theta);

    for k=0 to Matrix.n_rows m-1 do
      if k <> x_i.basic_idx then (
        let x_k = Matrix.get_row_var m k in
        let a_kj = Matrix.get m x_k.basic_idx x_j.idx in
        x_k.value <- Erat.(x_k.value + a_kj * theta);
      )
    done;

    begin
      (* now pivot the variables so that [x_j]'s coeff is -1 and so that
         other basic variables only depend on non-basic variables. *)
      let new_coeff = Q.(minus_one / a_ij) in
      for k=0 to Matrix.n_cols m-1 do
        Matrix.mult m x_i.basic_idx k new_coeff; (* update row of [x_i] *)
      done;
      assert Q.(Matrix.get m x_i.basic_idx x_j.idx = minus_one);

      (* make [x_i] non basic, and [x_j] basic *)
      x_j.basic_idx <- x_i.basic_idx;
      x_i.basic_idx <- -1;
      Matrix.set_row_var m x_j.basic_idx x_j;

      (* adjust other rows so they don't depend on [x_j] *)
      for k=0 to Matrix.n_rows m-1 do
        if k <> x_j.basic_idx then (
          let x_k = Matrix.get_row_var m k in
          assert (Var_state.is_basic x_k);

          let c_kj = Matrix.get m k x_j.idx in
          if Q.(c_kj <> zero) then (
            (* [m[k,j] != 0] indicates that basic variable [x_k] depends on
               [x_j], which is about to become basic. To avoid basic-basic
               dependency we replace [x_j] by its (new) definition *)

            for l=0 to Matrix.n_cols m-1 do
              if l<>x_j.idx then (
                let c_jl = Matrix.get m x_j.basic_idx l in
                (* so:
                   [x_k := c_kj * x_j + …], we want to eliminate [x_j],
                   and [x_j := … + c_jl * x_l + …].
                   therefore [x_j := … + c_jl * c_kl * x_l] *)
                Matrix.add m k l Q.(c_kj * c_jl);
              )
            done;

            Matrix.set m k x_j.idx Q.zero; (* [x_k] doesn't use [x_j] anymore *)
          )
        )
      done;
    end;

    assert (Var_state.is_basic x_j);
    assert (Var_state.is_n_basic x_i);
    (* Log.debugf 50 (fun k->k "post pivot: %a" pp self); *)
    _check_invariants_internal self;

    ()

  type unsat_cert =
    | E_bounds of {
        x: var_state;
        lower: bound;
        upper: bound;
      }
    | E_unsat_basic of {
        x: var_state;
        x_bound: (Op.t * bound);
        le: (num * V.t) list; (* definition of the basic var *)
        bounds: (Op.t * bound) V_map.t; (* bound for each variable in [le] *)
      }

  module Unsat_cert = struct
    type t = unsat_cert

    let lits = function
      | E_bounds b -> [b.lower.b_lit; b.upper.b_lit]
      | E_unsat_basic {x_bound=(_,x_bnd); bounds; x=_; le=_;} ->
        V_map.fold (fun _ (_,bnd) l -> bnd.b_lit :: l) bounds [x_bnd.b_lit]

    let pp out (self:t) =
      match self with
      | E_bounds {x;lower;upper} ->
        Fmt.fprintf out "(@[cert.unsat-bounds@ %a@ :lower %a@ :upper %a@])"
          Var_state.pp x Erat.pp lower.b_val Erat.pp upper.b_val
      | E_unsat_basic {x; x_bound; le; bounds} ->
        let pp_bnd out (v,(op,bnd)) =
          Fmt.fprintf out "(@[%a %s %a@])" Var.pp v (Op.to_string op) Erat.pp bnd.b_val
        in
        Fmt.fprintf out
          "(@[cert.unsat-basic@ %a@ @[:bound %a@] @[:le %a@]@ @[:le-bounds@ %a@]@])"
          Var_state.pp x pp_bnd (x.var,x_bound)
          Fmt.(Dump.list pp_bnd) (V_map.to_list bounds)
          Fmt.(Dump.list (Dump.pair pp_q_dbg V.pp)) le

    let bounds x ~lower ~upper : t = E_bounds {x; lower; upper}
    let unsat_basic x x_bound le bounds : t =
      E_unsat_basic {x; x_bound; le; bounds}
  end

  exception E_unsat of Unsat_cert.t

  let add_var self (v:V.t) : unit =
    ignore (find_or_create_n_basic_var_ self v : var_state);
    ()

  let add_constraint (self:t) (c:Constraint.t) (lit:V.lit) : unit =
    let open Constraint in

    let vs = find_or_create_n_basic_var_ self c.lhs in
    Log.debugf 5
      (fun k->k "(@[simplex2.add-constraint@ :var %a@ :c %a@])"
          Var_state.pp_name vs Constraint.pp c);

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
          let cert = Unsat_cert.bounds vs ~lower:new_bnd ~upper in
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
          let cert = Unsat_cert.bounds vs ~lower ~upper:new_bnd in
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
        let x_i = Matrix.get_row_var self.matrix i in
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

  (* TODO: certificate checker *)

  (* make a certificate from the row of basic variable [x_i] which is outside
     one of its bound, and whose row is tight on all non-basic variables.
     @param is_lower is true if the lower bound is not respected
     (i.e. [x_i] is too small) *)
  let cert_of_row_ (self:t) (x_i:var_state) (bnd:bound) ~is_lower : unsat_cert =
    Log.debugf 50 (fun k->k "(@[simplex.cert-of-row[lower: %B]@ x_i=%a@])"
                      is_lower Var_state.pp x_i);
    assert (Var_state.is_basic x_i);
    let le = ref [] in
    let bounds = ref V_map.empty in
    Vec.iteri
      (fun j x_j ->
        if j <> x_i.idx then (
          let c = Matrix.get self.matrix x_i.basic_idx j in
          if Q.(c <> zero) then (
            le := (c, x_j.var) :: !le;
            match is_lower, Q.(c > zero) with
            | true, true
            | false, false ->
              begin match x_j.u_bound with
                | Some u ->
                  let op = if Q.(u.b_val.eps_factor >= zero) then Op.Leq else Op.Lt in
                  bounds := V_map.add x_j.var (op, u) !bounds
                | None -> assert false (* we could increase [x_j]?! *)
              end
            | true, false
            | false, true ->
              begin match x_j.l_bound with
                | Some l ->
                  let op = if Q.(l.b_val.eps_factor <= zero) then Op.Geq else Op.Gt in
                  bounds := V_map.add x_j.var (op, l) !bounds
                | None -> assert false (* we could decrease [x_j]?! *)
              end
          )
        ))
      self.vars;

    let op =
      if is_lower then if Q.(bnd.b_val.eps_factor <= zero) then Op.Geq else Op.Gt
      else if Q.(bnd.b_val.eps_factor >= zero) then Op.Leq else Op.Lt
    in

    let cert = Unsat_cert.unsat_basic x_i (op, bnd) !le !bounds in
    cert

  (* main satisfiability check.
     page 15, figure 3.2 *)
  let check_exn (self:t) : unit =
    let exception Stop in
    Log.debugf 20 (fun k->k "(@[simplex2.check@ %a@])" pp_stats self);

    let m = self.matrix in
    try
      while true do
        _check_invariants_internal self;
        (* Log.debugf 50 (fun k->k "(@[simplex2.check.iter@ %a@])" pp self); *)

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
              let cert = cert_of_row_ self x_i bnd ~is_lower:true in
              raise (E_unsat cert)
          in
          assert (Var_state.is_n_basic x_j);

          (* line 9 *)
          Log.debugf 50
            (fun k->k "(@[simplex2.pivot@ :basic %a@ :n-basic %a@])"
                Var_state.pp x_i Var_state.pp x_j);
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
              let cert = cert_of_row_ self x_i bnd ~is_lower:false in
              raise (E_unsat cert)
          in
          assert (Var_state.is_n_basic x_j);

          (* line 14 *)
          Log.debugf 50
            (fun k->k "(@[simplex2.pivot@ :basic %a@ :n-basic %a@])"
                Var_state.pp x_i Var_state.pp x_j);
          pivot_and_update self x_i x_j bnd.b_val
        )
      done;
    with Stop ->
      Log.debugf 50 (fun k->k "(@[simplex2.check.done@])");
      ()

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

  let default_eps =
    let denom = 1 lsl 10 in
    Q.(one / of_int denom)

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
    let eps =
      Iter.fold
        (fun eps x ->
           assert Q.(eps >= zero);
           assert (Var_state.in_bounds_ x);

           let x_val = x.value in
           (*Log.debugf 50 (fun k->k "(@[solve-eps v.base=%a, v.eps=%a, emax=%a@])"
                             pp_q_dbg x_val.base pp_q_dbg x_val.eps_factor
                             pp_q_dbg eps);*)

           (* is lower bound *)
           let eps = match x.l_bound with
             | Some {b_val;_}
               when Q.(Erat.evaluate eps b_val > Erat.evaluate eps x_val) ->
               assert (Erat.(x.value >= b_val));
               assert (Q.(b_val.eps_factor > x.value.eps_factor));
               (* current epsilon is too big. we need to make it smaller
                  than [x.value - b_val].
                  - [b_val.base + eps * b_val.factor
                    <= x.base + eps * x.factor]
                  - [eps * (b_val.factor - x.factor) <= x.base - b_val.base]
                  - [eps <= (x.base - b_val.base) / (b_val.factor - x.factor)]
                  *)
               let new_eps =
                 Q.((x_val.base - b_val.base) /
                    (b_val.eps_factor - x_val.eps_factor))
               in
               Q.min eps new_eps
             | _ -> eps
           in
           (* upper bound *)
           let eps = match x.u_bound with
             | Some { b_val; _}
                 when Q.(Erat.evaluate eps b_val < Erat.evaluate eps x_val) ->
               assert (Erat.(x.value <= b_val));
               (* current epsilon is too big. we need to make it smaller
                  than [b_val - x.value].
                  - [x.base + eps * x.factor
                    <= b_val.base + eps * b_val.factor]
                  - [eps * (x.factor - b_val.factor) <= b_val.base - x.base]
                  - [eps <= (b_val.base - x.base) / (x.factor - b_val.factor)]
                  *)
               let new_eps =
                 Q.((b_val.base - x_val.base) /
                    (x_val.eps_factor - b_val.eps_factor))
               in
               Q.min eps new_eps
             | _ -> eps
           in
           eps)
        default_eps (Vec.to_seq self.vars)
    in
    if Q.(eps >= one) then Q.one else eps

  let model_ self =
    let eps = solve_epsilon self in
    Log.debugf 50 (fun k->k "(@[simplex2.model@ :epsilon-val %a@])" pp_q_dbg eps);
    let subst =
      Vec.to_seq self.vars
      |> Iter.fold
        (fun subst x ->
           let {base;eps_factor} = x.value in
           let v = Q.(base + eps * eps_factor) in
           V_map.add x.var v subst)
        V_map.empty
    in
    Log.debugf 5
      (fun k->k "(@[simplex2.model@ %a@])" Subst.pp subst);
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
