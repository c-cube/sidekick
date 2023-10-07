(** Fast Simplex for CDCL(T)

    We follow the paper "Integrating Simplex with DPLL(T )" from
    de Moura and Dutertre.
*)

open CCMonomorphic
module Linear_expr_intf = Linear_expr_intf
module Linear_expr = Linear_expr
module Predicate = Predicate
module Binary_op = Binary_op

module type INT = Sidekick_arith.INT
module type RATIONAL = Sidekick_arith.RATIONAL
module type VAR = Linear_expr_intf.VAR

(** Simplex operator *)
module Op = struct
  type t = Leq | Lt | Geq | Gt

  let[@inline] neg_sign = function
    | Leq -> Geq
    | Lt -> Gt
    | Geq -> Leq
    | Gt -> Lt

  let[@inline] not_ = function
    | Leq -> Gt
    | Lt -> Geq
    | Geq -> Lt
    | Gt -> Leq

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
  module Z : INT
  module Q : RATIONAL with type bigint = Z.t

  type num = Q.t
  (** Numbers *)

  module Constraint : sig
    type op = Op.t

    type t = { op: op; lhs: V.t; rhs: num }
    (** A constraint is the comparison of a variable to a constant. *)

    val mk : V.t -> op -> num -> t
    val leq : V.t -> num -> t
    val lt : V.t -> num -> t
    val geq : V.t -> num -> t
    val gt : V.t -> num -> t
    val pp : t Fmt.printer
  end

  module Subst : sig
    type t = num V_map.t

    val eval : t -> V.t -> Q.t option
    val to_iter : t -> (V.t * Q.t) Iter.t
    val pp : t Fmt.printer
    val to_string : t -> string
  end

  type t

  val create : ?stat:Stat.t -> unit -> t
  (** Create a new simplex. *)

  val push_level : t -> unit
  val pop_levels : t -> int -> unit

  val define : ?is_int:bool -> t -> V.t -> (num * V.t) list -> unit
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

  type ev_on_propagate = V.lit -> reason:V.lit list -> unit

  val add_var : ?is_int:bool -> t -> V.t -> unit
  (** Make sure the variable exists in the simplex. *)

  val add_constraint :
    ?is_int:bool ->
    on_propagate:ev_on_propagate ->
    t ->
    Constraint.t ->
    V.lit ->
    unit
  (** Add a constraint to the simplex.

      This is removed upon backtracking by default.
      @param is_int declares whether the constraint's variable is an integer
      @raise Unsat if it's immediately obvious that this is not satisfiable.
  *)

  val declare_bound : ?is_int:bool -> t -> Constraint.t -> V.lit -> unit
  (** Declare that this constraint exists and map it to a literal,
      so we can possibly propagate it later.
      Unlike {!add_constraint} this does {b NOT} assert that the constraint
      is true *)

  val check_exn : on_propagate:(V.lit -> reason:V.lit list -> unit) -> t -> unit
  (** Check the whole simplex for satisfiability.
      @param on_propagate is called with arguments [lit, reason] whenever
      [reason => lit] is found to be true by the simplex.
      @raise Unsat if the constraints are not satisfiable. *)

  type result = Sat of Subst.t | Unsat of Unsat_cert.t

  val check : on_propagate:(V.lit -> reason:V.lit list -> unit) -> t -> result
  (** Call {!check_exn} and return a model or a proof of unsat.
      This does {b NOT} enforce that integer variables map to integer values. *)

  val check_branch_and_bound :
    on_propagate:(V.lit -> reason:V.lit list -> unit) ->
    max_tree_nodes:int ->
    t ->
    result option
  (** Try to solve and respect the integer constraints. *)

  val n_vars : t -> int
  val n_rows : t -> int

  (**/**)

  val _check_invariants : t -> unit
  (* check internal invariants *)

  val _check_cert : unsat_cert -> unit

  (**/**)
end

module type ARG = sig
  module Z : INT
  module Q : RATIONAL with type bigint = Z.t
  module Var : VAR

  val mk_lit : Var.t -> Op.t -> Q.t -> Var.lit
  (** Create new literals *)
end

(* TODO: (optim): page 14, paragraph 2: we could detect which variables occur in no
   atom after preprocessing; then these variables can be "inlined" (removed
   by Gaussian elimination) as a preprocessing proof_rule, and this removes one column
   and maybe one row if it was basic. *)

module Make (Arg : ARG) :
  S with module V = Arg.Var and module Z = Arg.Z and module Q = Arg.Q = struct
  module V = Arg.Var
  module V_map = CCMap.Make (V)
  module Z = Arg.Z
  module Q = Arg.Q

  type lit = V.lit
  type num = Q.t

  let pp_q_dbg = Q.pp_approx 1

  module Constraint = struct
    type op = Op.t

    type t = { op: op; lhs: V.t; rhs: num }
    (** A constraint is the comparison of a variable to a constant. *)

    let pp out (self : t) =
      Fmt.fprintf out "(@[%a %s@ %a@])" V.pp self.lhs (Op.to_string self.op)
        pp_q_dbg self.rhs

    let mk lhs op rhs : t = { lhs; op; rhs }
    let leq lhs rhs = { lhs; rhs; op = Op.Leq }
    let lt lhs rhs = { lhs; rhs; op = Op.Lt }
    let geq lhs rhs = { lhs; rhs; op = Op.Geq }
    let gt lhs rhs = { lhs; rhs; op = Op.Gt }
  end

  module Subst = struct
    type t = num V_map.t

    let eval self t = V_map.get t self
    let to_iter self f = V_map.iter (fun k v -> f (k, v)) self

    let pp out (self : t) : unit =
      let pp_pair out (v, n) =
        Fmt.fprintf out "(@[%a := %a@])" V.pp v pp_q_dbg n
      in
      Fmt.fprintf out "{@[%a@]}" (Fmt.iter pp_pair) (V_map.to_iter self)

    let to_string = Fmt.to_string pp
  end

  type erat = {
    base: num;  (** reference number *)
    eps_factor: num;  (** coefficient for epsilon, the infinitesimal *)
  }
  (** An extended rational, used to introduce ε so we can use strict
      comparisons in an algorithm designed to handle >= only.

      In a way, an extended rational is a tuple `(base, factor)`
      ordered lexicographically. *)

  (** Epsilon-rationals, used for strict bounds *)
  module Erat = struct
    type t = erat

    let zero : t = { base = Q.zero; eps_factor = Q.zero }

    let[@inline] make base eps_factor : t =
      if Q.is_real base then
        { base; eps_factor }
      else
        { base; eps_factor = Q.zero }

    let[@inline] make_q x = make x Q.zero
    let[@inline] base t = t.base
    let[@inline] eps_factor t = t.eps_factor
    let[@inline] ( * ) k e = make Q.(k * e.base) Q.(k * e.eps_factor)
    let[@inline] ( / ) e k = make Q.(e.base / k) Q.(e.eps_factor / k)

    let[@inline] ( + ) e1 e2 =
      make Q.(e1.base + e2.base) Q.(e1.eps_factor + e2.eps_factor)

    let[@inline] ( - ) e1 e2 =
      make Q.(e1.base - e2.base) Q.(e1.eps_factor - e2.eps_factor)

    let[@inline] compare e1 e2 =
      match Q.compare e1.base e2.base with
      | 0 -> Q.compare e1.eps_factor e2.eps_factor
      | x -> x

    let[@inline] ( < ) a b = compare a b < 0
    let[@inline] ( <= ) a b = compare a b <= 0
    let[@inline] ( > ) a b = compare a b > 0
    let[@inline] ( >= ) a b = compare a b >= 0
    let[@inline] ( = ) a b = compare a b = 0
    let plus_inf = make Q.infinity Q.zero
    let minus_inf = make Q.minus_infinity Q.zero

    let[@inline] min x y =
      if x <= y then
        x
      else
        y

    let[@inline] max x y =
      if x >= y then
        x
      else
        y

    let[@inline] evaluate (epsilon : Q.t) (e : t) : Q.t =
      Q.(e.base + (epsilon * e.eps_factor))

    let pp out e : unit =
      if Q.equal Q.zero (eps_factor e) then
        pp_q_dbg out (base e)
      else
        Fmt.fprintf out "(@[<h>%a + @<1>ε * %a@])" pp_q_dbg (base e) pp_q_dbg
          (eps_factor e)
  end

  type bound = { b_val: erat; b_lit: lit }
  type is_lower = bool

  type var_state = {
    var: V.t;
    mutable value: erat;
    idx: int;  (** index in {!t.vars} *)
    mutable basic_idx: int;
        (** index of the row in the matrix, if any. -1 otherwise *)
    mutable l_bound: bound option;
    mutable u_bound: bound option;
    mutable all_bound_lits: (is_lower * bound) list;
        (** all known literals on this var *)
    mutable is_int: bool;
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
    val iter_rows : ?skip:int -> t -> (int -> var_state -> unit) -> unit
    val iter_cols : ?skip:int -> t -> (int -> unit) -> unit

    val add_column : t -> unit
    (** Add a non-basic variable (only adds a column) *)

    val add_row_and_column :
      t -> f:(row_idx:int -> col_idx:int -> var_state) -> var_state
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
    type row = { mutable vs: var_state; cols: num Vec.t }
    type t = { mutable n_cols: int; rows: row Vec.t }

    let create () : t = { n_cols = 0; rows = Vec.create () }
    let[@inline] n_rows self = Vec.size self.rows
    let[@inline] n_cols self = self.n_cols

    let pp out self =
      Fmt.fprintf out "@[<v1>{matrix[%dx%d]@," (n_rows self) (n_cols self);

      (* header *)
      let ppi out i =
        Fmt.string out @@ CCString.pad ~side:`Left 6 @@ Printf.sprintf "v%d" i
      in
      Fmt.fprintf out "{@[<hov2>%9s: %a@]}" "vars"
        (Fmt.iter ~sep:(Fmt.return "@ ") ppi)
        CCInt.(0 -- (n_cols self - 1));

      Vec.iteri self.rows ~f:(fun i row ->
          let hd =
            CCString.pad ~side:`Left 6
            @@ Printf.sprintf "r%d (v%d)" i row.vs.idx
          in
          Fmt.fprintf out "@,{@[<hov2>%9s: %a@]}" hd
            (Fmt.iter ~sep:(Fmt.return "@ ") (Q.pp_approx 6))
            (Vec.to_iter row.cols));
      Fmt.fprintf out "@;<0 -1>}@]"

    let to_string = Fmt.to_string pp

    let add_column self =
      self.n_cols <- 1 + self.n_cols;
      Vec.iter self.rows ~f:(fun r -> Vec.push r.cols Q.zero)

    let add_row_and_column self ~f : var_state =
      let n = n_rows self in
      let j = n_cols self in
      add_column self;
      let cols = Vec.make (j + 1) Q.zero in
      for _k = 0 to j do
        Vec.push cols Q.zero
      done;
      let vs = f ~row_idx:n ~col_idx:j in
      let row = { vs; cols } in
      Vec.push self.rows row;
      vs

    let[@inline] get_row_var self i = (Vec.get self.rows i).vs
    let[@inline] set_row_var self i v = (Vec.get self.rows i).vs <- v
    let[@inline] get self i j : num = Vec.get (Vec.get self.rows i).cols j

    let[@inline] set self i j n : unit =
      let r = Vec.get self.rows i in
      Vec.set r.cols j n

    let[@inline] iter_rows ?(skip = ~-1) (self : t) f : unit =
      Vec.iteri self.rows ~f:(fun i row -> if i <> skip then f i row.vs)

    let[@inline] iter_cols ?(skip = ~-1) (self : t) f : unit =
      for i = 0 to n_cols self - 1 do
        if i <> skip then f i
      done

    (** add [n] to [m_ij] *)
    let add self i j n : unit =
      let r = Vec.get self.rows i in
      Vec.set r.cols j Q.(Vec.get r.cols j + n)

    (** multiply [m_ij] by [c] *)
    let mult self i j c : unit =
      let r = Vec.get self.rows i in
      let n_j = Vec.get r.cols j in
      if Q.(n_j <> zero) then Vec.set r.cols j Q.(n_j * c)
  end

  module Var_state = struct
    type t = var_state

    let ( == ) : t -> t -> bool = Containers.Stdlib.( == )
    let ( != ) : t -> t -> bool = Containers.Stdlib.( != )
    let[@inline] is_basic (self : t) : bool = self.basic_idx >= 0
    let[@inline] is_n_basic (self : t) : bool = self.basic_idx < 0

    let in_bounds_ self =
      (match self.l_bound with
      | None -> true
      | Some b -> Erat.(self.value >= b.b_val))
      &&
      match self.u_bound with
      | None -> true
      | Some b -> Erat.(self.value <= b.b_val)

    let pp_name out self = Fmt.fprintf out "v%d" self.idx

    let pp out self =
      let bnd_status =
        if in_bounds_ self then
          ""
        else
          "(oob)"
      in
      let pp_bnd what out = function
        | None -> ()
        | Some b -> Fmt.fprintf out "@ @[%s %a@]" what Erat.pp b.b_val
      and pp_basic_idx out () =
        if self.basic_idx < 0 then
          ()
        else
          Fmt.int out self.basic_idx
      in
      Fmt.fprintf out "(@[v%d[%s%a]%s@ :value %a%a%a@ :t-var %a@])" self.idx
        (if is_basic self then
          "B"
        else
          "N")
        pp_basic_idx () bnd_status Erat.pp self.value (pp_bnd ":lower")
        self.l_bound (pp_bnd ":upper") self.u_bound V.pp self.var
  end

  type bound_assertion = var_state * [ `Upper | `Lower ] * bound option

  type t = {
    matrix: Matrix.t;
    vars: var_state Vec.t;  (** index -> var with this index *)
    mutable var_tbl: var_state V_map.t;  (** var -> its state *)
    bound_stack: bound_assertion Backtrack_stack.t;
    undo_stack: (unit -> unit) Backtrack_stack.t;
    stat_check: int Stat.counter;
    stat_unsat: int Stat.counter;
    stat_define: int Stat.counter;
    stat_propagate: int Stat.counter;
    stat_vars: int Stat.counter;
  }

  let push_level self : unit =
    Log.debug 30 "(simplex.push-level)";
    Backtrack_stack.push_level self.bound_stack;
    Backtrack_stack.push_level self.undo_stack

  let pop_levels self n : unit =
    Log.debugf 30 (fun k -> k "(simplex.pop-levels %d)" n);
    Backtrack_stack.pop_levels self.bound_stack n ~f:(fun (var, kind, bnd) ->
        match kind with
        | `Upper -> var.u_bound <- bnd
        | `Lower -> var.l_bound <- bnd);
    Backtrack_stack.pop_levels self.undo_stack n ~f:(fun f -> f ());
    ()

  let n_vars self = Vec.size self.vars
  let n_rows self = Matrix.n_rows self.matrix

  let pp_stats out (self : t) : unit =
    Fmt.fprintf out "(@[simplex@ :n-vars %d@ :n-rows %d@])" (Vec.size self.vars)
      (Matrix.n_rows self.matrix)

  let pp out (self : t) : unit =
    Fmt.fprintf out
      "(@[simplex@ @[<1>:vars@ [@[<hov>%a@]]@]@ @[<1>:matrix@ %a@]@])"
      (Vec.pp Var_state.pp) self.vars Matrix.pp self.matrix

  (** for debug purposes *)
  let _check_invariants self : unit =
    Vec.iteri self.vars ~f:(fun i v -> assert (v.idx = i));
    let n = Vec.size self.vars in
    assert (Matrix.n_rows self.matrix = 0 || Matrix.n_cols self.matrix = n);
    Matrix.iter_rows self.matrix (fun i x_i ->
        assert (Var_state.is_basic x_i);
        assert (x_i.basic_idx = i);
        assert (Q.(Matrix.get self.matrix x_i.basic_idx x_i.idx = minus_one));

        (* basic vars are only defined in terms of non-basic vars *)
        Vec.iteri self.vars ~f:(fun j x_j ->
            if Var_state.(x_i != x_j) && Q.(Matrix.get self.matrix i j <> zero)
            then
              assert (Var_state.is_n_basic x_j));

        (* sum of each row must be 0 *)
        let sum =
          Vec.fold
            (fun sum v ->
              Erat.(sum + (Matrix.get self.matrix i v.idx * v.value)))
            Erat.zero self.vars
        in
        Log.debugf 50 (fun k -> k "row %d: sum %a" i Erat.pp sum);
        assert (Erat.(sum = zero)));
    ()

  (** for internal checking *)
  let[@inline] _check_invariants_internal self =
    if false (* FUDGE *) then _check_invariants self

  let[@inline] has_var_ (self : t) x : bool = V_map.mem x self.var_tbl

  let[@inline] find_var_ (self : t) x : var_state =
    try V_map.find x self.var_tbl
    with Not_found ->
      Error.errorf "variable `%a`@ is not in the simplex" V.pp x

  (** define [x] as a basic variable *)
  let define ?(is_int = false) (self : t) (x : V.t) (le : _ list) : unit =
    if has_var_ self x then
      Error.errorf "Simplex: cannot define `%a`,@ already a variable" V.pp x;
    Stat.incr self.stat_define;
    (* Log.debugf 50 (fun k->k "define-in: %a" pp self); *)
    let le = List.map (fun (q, v) -> q, find_var_ self v) le in

    (* initial value for the new variable *)
    let value =
      List.fold_left (fun sum (c, v) -> Erat.(sum + (c * v.value))) Erat.zero le
    in

    let vs =
      Matrix.add_row_and_column self.matrix ~f:(fun ~row_idx ~col_idx ->
          {
            var = x;
            value;
            idx = col_idx;
            basic_idx = row_idx;
            l_bound = None;
            u_bound = None;
            all_bound_lits = [];
            is_int;
          })
    in
    Log.debugf 5 (fun k ->
        k "(@[simplex.define@ @[v%d :var %a@]@ :linexpr %a@])" vs.idx V.pp x
          Fmt.(Dump.(list @@ pair pp_q_dbg Var_state.pp_name))
          le);

    assert (Var_state.is_basic vs);
    assert (Var_state.(Matrix.get_row_var self.matrix vs.basic_idx == vs));
    Vec.push self.vars vs;
    self.var_tbl <- V_map.add x vs self.var_tbl;

    (* set coefficients in the matrix's new row: [-x + le = 0] *)
    Matrix.set self.matrix vs.basic_idx vs.idx Q.minus_one;
    List.iter
      (fun (coeff, v2) ->
        assert (Containers.Stdlib.(v2 != vs));

        if Var_state.is_basic v2 then
          (* [v2] is also basic, so instead of depending on it,
             we depend on its definition in terms of non-basic variables. *)
          Matrix.iter_cols ~skip:v2.idx self.matrix (fun k ->
              let v2_jk = Matrix.get self.matrix v2.basic_idx k in
              if Q.(v2_jk <> zero) then (
                let x_k = Vec.get self.vars k in
                assert (Var_state.is_n_basic x_k);

                (* [v2 := v2_jk * x_k + …], so [v := … + coeff * v2_jk * x_k] *)
                Matrix.add self.matrix vs.basic_idx k Q.(coeff * v2_jk)
              ))
        else
          (* directly add coefficient with non-basic var [v2] *)
          Matrix.add self.matrix vs.basic_idx v2.idx coeff)
      le;

    (* Log.debugf 50 (fun k->k "post-define: %a" pp self); *)
    _check_invariants_internal self;
    ()

  (** find the state for [x], or add [x] as a non-basic variable *)
  let find_or_create_n_basic_var_ ~is_int (self : t) (x : V.t) : var_state =
    try
      let v = V_map.find x self.var_tbl in
      if is_int then v.is_int <- true;
      v
    with Not_found ->
      Stat.incr self.stat_vars;
      Matrix.add_column self.matrix;
      let vs =
        {
          idx = Vec.size self.vars;
          basic_idx = -1;
          var = x;
          l_bound = None;
          u_bound = None;
          value = Erat.zero;
          all_bound_lits = [];
          is_int;
        }
      in
      assert (Var_state.is_n_basic vs);
      self.var_tbl <- V_map.add x vs self.var_tbl;
      Vec.push self.vars vs;
      vs

  (** update the simplex so that non-basic [x] is now assigned value [n].
     See page 14, figure 3.1.
  *)
  let update_n_basic (self : t) (x : var_state) (v : erat) : unit =
    assert (Var_state.is_n_basic x);
    Log.debugf 50 (fun k ->
        k "(@[<hv>simplex.update-n-basic@ %a@ :new-val %a@])" Var_state.pp x
          Erat.pp v);
    _check_invariants_internal self;

    let m = self.matrix in
    let i = x.idx in

    let diff = Erat.(v - x.value) in

    Matrix.iter_rows m (fun j x_j ->
        let a_ji = Matrix.get m j i in
        assert (Var_state.is_basic x_j);
        (* value of [x_j] by [a_ji * diff] *)
        let new_val = Erat.(x_j.value + (a_ji * diff)) in
        (* Log.debugf 50 (fun k->k "new-val %a@ := %a" Var_state.pp x_j Erat.pp new_val); *)
        x_j.value <- new_val);
    x.value <- v;
    _check_invariants_internal self;
    ()

  (** pivot [x_i] (basic) and [x_j] (non-basic), setting value of [x_i]
     to [v] at the same time.
     See page 14, figure 3.1 *)
  let pivot_and_update (self : t) (x_i : var_state) (x_j : var_state) (v : erat)
      : unit =
    assert (Var_state.is_basic x_i);
    assert (Var_state.is_n_basic x_j);
    _check_invariants_internal self;

    let m = self.matrix in
    let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
    assert (Q.sign a_ij <> 0);
    let theta = Erat.((v - x_i.value) / a_ij) in
    x_i.value <- v;
    x_j.value <- Erat.(x_j.value + theta);

    Matrix.iter_rows m ~skip:x_i.basic_idx (fun _k x_k ->
        let a_kj = Matrix.get m x_k.basic_idx x_j.idx in
        x_k.value <- Erat.(x_k.value + (a_kj * theta)));

    ((* now pivot the variables so that [x_j]'s coeff is -1 and so that
        other basic variables only depend on non-basic variables. *)
     let new_coeff = Q.(minus_one / a_ij) in
     Matrix.iter_cols m (fun k ->
         Matrix.mult m x_i.basic_idx k new_coeff (* update row of [x_i] *));
     assert (Q.(Matrix.get m x_i.basic_idx x_j.idx = minus_one));

     (* make [x_i] non basic, and [x_j] basic *)
     x_j.basic_idx <- x_i.basic_idx;
     x_i.basic_idx <- -1;
     Matrix.set_row_var m x_j.basic_idx x_j;

     (* adjust other rows so they don't depend on [x_j] *)
     Matrix.iter_rows ~skip:x_j.basic_idx m (fun k x_k ->
         assert (Var_state.is_basic x_k);

         let c_kj = Matrix.get m k x_j.idx in
         if Q.(c_kj <> zero) then (
           (* [m[k,j] != 0] indicates that basic variable [x_k] depends on
                [x_j], which is about to become basic. To avoid basic-basic
                dependency we replace [x_j] by its (new) definition *)
           Matrix.iter_cols m (fun l ->
               if l <> x_j.idx then (
                 let c_jl = Matrix.get m x_j.basic_idx l in
                 (* so:
                      [x_k := c_kj * x_j + …], we want to eliminate [x_j],
                      and [x_j := … + c_jl * x_l + …].
                      therefore [x_j := … + c_jl * c_kl * x_l] *)
                 Matrix.add m k l Q.(c_kj * c_jl)
               ));

           Matrix.set m k x_j.idx Q.zero (* [x_k] doesn't use [x_j] anymore *)
         )));

    assert (Var_state.is_basic x_j);
    assert (Var_state.is_n_basic x_i);
    (* Log.debugf 50 (fun k->k "post pivot: %a" pp self); *)
    _check_invariants_internal self;

    ()

  type unsat_cert =
    | E_bounds of { x: var_state; lower: bound; upper: bound }
    | E_unsat_basic of {
        x: var_state;
        x_bound: Op.t * bound;
        le: (num * V.t) list; (* definition of the basic var *)
        bounds: (Op.t * bound) V_map.t; (* bound for each variable in [le] *)
      }
    | E_branch_and_bound of {
        x: var_state; (* is_int: true *)
        middle: Q.t;
        low: Z.t; (* floor middle *)
        high: Z.t; (* floor middle+1 *)
        pr_low: unsat_cert; (* proof for x <= low *)
        pr_high: unsat_cert; (* proof for x >= high *)
      }

  module Unsat_cert = struct
    type t = unsat_cert

    let rec lits = function
      | E_bounds b -> [ b.lower.b_lit; b.upper.b_lit ]
      | E_unsat_basic { x_bound = _, x_bnd; bounds; x = _; le = _ } ->
        V_map.fold (fun _ (_, bnd) l -> bnd.b_lit :: l) bounds [ x_bnd.b_lit ]
      | E_branch_and_bound { pr_low; pr_high; _ } ->
        List.rev_append (lits pr_low) (lits pr_high)

    let rec pp out (self : t) : unit =
      match self with
      | E_bounds { x; lower; upper } ->
        Fmt.fprintf out "(@[cert.unsat-bounds@ %a@ :lower %a@ :upper %a@])"
          Var_state.pp x Erat.pp lower.b_val Erat.pp upper.b_val
      | E_unsat_basic { x; x_bound; le; bounds } ->
        let pp_bnd out (v, (op, bnd)) =
          Fmt.fprintf out "(@[%a %s %a@])" V.pp v (Op.to_string op) Erat.pp
            bnd.b_val
        in
        Fmt.fprintf out
          "(@[cert.unsat-basic@ %a@ @[:bound %a@] @[:le %a@]@ @[:le-bounds@ \
           %a@]@])"
          Var_state.pp x pp_bnd (x.var, x_bound)
          Fmt.(Dump.list pp_bnd)
          (V_map.to_list bounds)
          Fmt.(Dump.list (Dump.pair pp_q_dbg V.pp))
          le
      | E_branch_and_bound { x; middle; pr_low; pr_high; low; high } ->
        Fmt.fprintf out
          "(@[cert.unsat.branch-and-bound@ %a@ @[:middle %a@] @[:low %a@ %a@]@ \
           @[:high %a@ %a@]@])"
          Var_state.pp x Q.pp middle Z.pp low pp pr_low Z.pp high pp pr_high

    let bounds x ~lower ~upper : t = E_bounds { x; lower; upper }

    let unsat_basic x x_bound le bounds : t =
      E_unsat_basic { x; x_bound; le; bounds }
  end

  exception E_unsat of Unsat_cert.t

  type ev_on_propagate = lit -> reason:lit list -> unit

  let add_var ?(is_int = false) self (v : V.t) : unit =
    ignore (find_or_create_n_basic_var_ ~is_int self v : var_state);
    ()

  (** gather all relevant lower (resp. upper) bounds for the definition
      of the basic variable [x_i], and collect each relevant variable
      with [map] into a list.
      @param get_lower if true, means we select lower bounds of variables
      with positive coeffs, and upper bounds of variables with negative coeffs. *)
  let gather_bounds_of_row_ (self : t) (x_i : var_state) ~map ~get_lower :
      _ list * _ =
    assert (Var_state.is_basic x_i);
    let map_res = ref [] in
    let bounds = ref V_map.empty in
    Vec.iteri self.vars ~f:(fun j x_j ->
        if j <> x_i.idx then (
          let c = Matrix.get self.matrix x_i.basic_idx j in
          if Q.(c <> zero) then (
            match get_lower, Q.(c > zero) with
            | true, true | false, false ->
              (match x_j.l_bound with
              | Some l ->
                map_res := map c x_j l :: !map_res;
                let op =
                  if Q.(l.b_val.eps_factor <= zero) then
                    Op.Geq
                  else
                    Op.Gt
                in
                bounds := V_map.add x_j.var (op, l) !bounds
              | None -> assert false (* we could decrease [x_j]?! *))
            | true, false | false, true ->
              (match x_j.u_bound with
              | Some u ->
                map_res := map c x_j u :: !map_res;
                let op =
                  if Q.(u.b_val.eps_factor >= zero) then
                    Op.Leq
                  else
                    Op.Lt
                in
                bounds := V_map.add x_j.var (op, u) !bounds
              | None -> assert false (* we could increase [x_j]?! *))
          )
        ));
    !map_res, !bounds

  let add_constraint ?(is_int = false) ~on_propagate (self : t)
      (c : Constraint.t) (lit : lit) : unit =
    let open Constraint in
    let vs = find_or_create_n_basic_var_ ~is_int self c.lhs in
    Log.debugf 5 (fun k ->
        k "(@[simplex.add-constraint@ :var %a@ :c %a@])" Var_state.pp_name vs
          Constraint.pp c);

    let is_lower_bnd, new_bnd_val =
      match c.op with
      | Leq -> false, Erat.make_q c.rhs
      | Lt -> false, Erat.make c.rhs Q.minus_one
      | Geq -> true, Erat.make_q c.rhs
      | Gt -> true, Erat.make c.rhs Q.one
    in
    let new_bnd = { b_val = new_bnd_val; b_lit = lit } in
    if is_lower_bnd then (
      match vs.l_bound, vs.u_bound with
      | _, Some upper when Erat.(new_bnd.b_val > upper.b_val) ->
        (* [b_val <= x <= upper], but [b_val > upper] *)
        let cert = Unsat_cert.bounds vs ~lower:new_bnd ~upper in
        Stat.incr self.stat_unsat;
        raise (E_unsat cert)
      | Some lower, _ when Erat.(lower.b_val >= new_bnd.b_val) ->
        () (* subsumed by existing constraint, do nothing *)
      | _ ->
        (* save current bound *)
        Backtrack_stack.push self.bound_stack (vs, `Lower, vs.l_bound);
        vs.l_bound <- Some new_bnd;

        (* propagate *)
        List.iter
          (fun (is_lower', bnd) ->
            if is_lower' && Erat.(bnd.b_val < new_bnd.b_val) then (
              (* subsumed *)
              Stat.incr self.stat_propagate;
              on_propagate bnd.b_lit ~reason:[ new_bnd.b_lit ]
            ) else if (not is_lower') && Erat.(bnd.b_val < new_bnd.b_val) then (
              (* incompatible upper bound *)
              match V.not_lit bnd.b_lit with
              | Some l' ->
                Stat.incr self.stat_propagate;
                on_propagate l' ~reason:[ new_bnd.b_lit ]
              | None -> ()
            ))
          vs.all_bound_lits;

        if Var_state.is_n_basic vs && Erat.(vs.value < new_bnd.b_val) then
          (* line 5: need to update non-basic variable *)
          update_n_basic self vs new_bnd.b_val
    ) else (
      match vs.l_bound, vs.u_bound with
      | Some lower, _ when Erat.(new_bnd.b_val < lower.b_val) ->
        (* [lower <= x <= b_val], but [b_val < lower] *)
        let cert = Unsat_cert.bounds vs ~lower ~upper:new_bnd in
        Stat.incr self.stat_unsat;
        raise (E_unsat cert)
      | _, Some upper when Erat.(upper.b_val <= new_bnd.b_val) ->
        () (* subsumed *)
      | _ ->
        Backtrack_stack.push self.bound_stack (vs, `Upper, vs.u_bound);
        vs.u_bound <- Some new_bnd;

        (* propagate *)
        List.iter
          (fun (is_lower', bnd) ->
            if (not is_lower') && Erat.(bnd.b_val > new_bnd.b_val) then (
              (* subsumed *)
              Stat.incr self.stat_propagate;
              on_propagate bnd.b_lit ~reason:[ new_bnd.b_lit ]
            ) else if is_lower' && Erat.(bnd.b_val > new_bnd.b_val) then (
              (* incompatible lower bound *)
              match V.not_lit bnd.b_lit with
              | Some l' ->
                Stat.incr self.stat_propagate;
                on_propagate l' ~reason:[ new_bnd.b_lit ]
              | None -> ()
            ))
          vs.all_bound_lits;

        if Var_state.is_n_basic vs && Erat.(vs.value > new_bnd.b_val) then
          (* line 5: need to update non-basic variable *)
          update_n_basic self vs new_bnd.b_val
    )

  let declare_bound ?(is_int = false) (self : t) (c : Constraint.t) (lit : lit)
      : unit =
    let vs = find_or_create_n_basic_var_ ~is_int self c.lhs in
    Log.debugf 10 (fun k ->
        k "(@[simplex.declare-bound@ %a@ :lit %a@])" Constraint.pp c V.pp_lit
          lit);

    let is_lower_bnd, new_bnd_val =
      match c.op with
      | Leq -> false, Erat.make_q c.rhs
      | Lt -> false, Erat.make c.rhs Q.minus_one
      | Geq -> true, Erat.make_q c.rhs
      | Gt -> true, Erat.make c.rhs Q.one
    in
    let new_bnd = is_lower_bnd, { b_val = new_bnd_val; b_lit = lit } in
    vs.all_bound_lits <- new_bnd :: vs.all_bound_lits

  (** try to find basic variable that doesn't respect one of its bounds *)
  let find_basic_var_ (self : t) :
      (var_state * [ `Lower | `Upper ] * bound) option =
    let exception Found of var_state * [ `Lower | `Upper ] * bound in
    try
      Matrix.iter_rows self.matrix (fun _i x_i ->
          let v_i = x_i.value in
          match x_i.l_bound, x_i.u_bound with
          | Some l, _ when Erat.(l.b_val > v_i) ->
            raise_notrace (Found (x_i, `Lower, l))
          | _, Some u when Erat.(u.b_val < v_i) ->
            raise_notrace (Found (x_i, `Upper, u))
          | _ -> ());
      None
    with Found (v, k, bnd) -> Some (v, k, bnd)

  let find_n_basic_var_ (self : t) ~f : var_state option =
    let rec aux j =
      if j >= Vec.size self.vars then
        None
      else (
        let x_j = Vec.get self.vars j in
        if Var_state.is_n_basic x_j && f x_j then
          Some x_j
        else
          aux (j + 1)
      )
    in
    aux 0

  (** true if [x.value < x.u_bound] *)
  let has_upper_slack (x : var_state) : bool =
    match x.u_bound with
    | None -> true
    | Some bnd -> Erat.(x.value < bnd.b_val)

  (** true if [x.value > x.l_bound] *)
  let has_lower_slack (x : var_state) : bool =
    match x.l_bound with
    | None -> true
    | Some bnd -> Erat.(x.value > bnd.b_val)

  (** make a certificate from the row of basic variable [x_i] which is outside
      one of its bound, and whose row is tight on all non-basic variables.
      @param is_lower is true if the lower bound is not respected
     (i.e. [x_i] is too small) *)
  let cert_of_row_ (self : t) (x_i : var_state) (bnd : bound) ~is_lower :
      unsat_cert =
    Log.debugf 50 (fun k ->
        k "(@[simplex.cert-of-row[lower: %B]@ x_i=%a@])" is_lower Var_state.pp
          x_i);
    assert (Var_state.is_basic x_i);
    let le, bounds =
      (* we get explanations for an (implied) upper bound
         if [bnd] is a lower bound, and conversely *)
      gather_bounds_of_row_ self x_i ~get_lower:(not is_lower)
        ~map:(fun c v _ -> c, v.var)
    in

    let op =
      if is_lower then
        if Q.(bnd.b_val.eps_factor <= zero) then
          Op.Geq
        else
          Op.Gt
      else if Q.(bnd.b_val.eps_factor >= zero) then
        Op.Leq
      else
        Op.Lt
    in

    let cert = Unsat_cert.unsat_basic x_i (op, bnd) le bounds in
    cert

  (** main satisfiability check.
      page 15, figure 3.2 *)
  let check_exn ~on_propagate:_ (self : t) : unit =
    let exception Stop in
    Log.debugf 20 (fun k -> k "(@[simplex.check@ %a@])" pp_stats self);
    Stat.incr self.stat_check;

    let m = self.matrix in
    try
      while true do
        _check_invariants_internal self;

        (* Log.debugf 50 (fun k->k "(@[simplex.check.iter@ %a@])" pp self); *)

        (* basic variable that doesn't respect its bound *)
        let x_i, is_lower, bnd =
          match find_basic_var_ self with
          | Some (x, `Lower, bnd) -> x, true, bnd
          | Some (x, `Upper, bnd) -> x, false, bnd
          | None -> raise_notrace Stop
          (* line 4: we are done *)
        in

        if is_lower then (
          (* line 5 *)
          let x_j =
            match
              find_n_basic_var_ self ~f:(fun x_j ->
                  let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
                  (Q.sign a_ij > 0 && has_upper_slack x_j)
                  || (Q.sign a_ij < 0 && has_lower_slack x_j))
            with
            | Some x -> x
            | None ->
              let cert = cert_of_row_ self x_i bnd ~is_lower:true in
              Stat.incr self.stat_unsat;
              raise (E_unsat cert)
          in
          assert (Var_state.is_n_basic x_j);

          (* line 9 *)
          Log.debugf 50 (fun k ->
              k "(@[simplex.pivot@ :basic %a@ :n-basic %a@])" Var_state.pp x_i
                Var_state.pp x_j);
          pivot_and_update self x_i x_j bnd.b_val
        ) else (
          (* line 10 *)
          let x_j =
            match
              find_n_basic_var_ self ~f:(fun x_j ->
                  let a_ij = Matrix.get m x_i.basic_idx x_j.idx in
                  (Q.sign a_ij < 0 && has_upper_slack x_j)
                  || (Q.sign a_ij > 0 && has_lower_slack x_j))
            with
            | Some x -> x
            | None ->
              let cert = cert_of_row_ self x_i bnd ~is_lower:false in
              Stat.incr self.stat_unsat;
              raise (E_unsat cert)
          in
          assert (Var_state.is_n_basic x_j);

          (* line 14 *)
          Log.debugf 50 (fun k ->
              k "(@[simplex.pivot@ :basic %a@ :n-basic %a@])" Var_state.pp x_i
                Var_state.pp x_j);
          pivot_and_update self x_i x_j bnd.b_val
        )
      done
    with Stop ->
      Log.debugf 50 (fun k -> k "(@[simplex.check.done@])");
      ()

  let create ?(stat = Stat.global) () : t =
    let self =
      {
        matrix = Matrix.create ();
        vars = Vec.create ();
        var_tbl = V_map.empty;
        bound_stack = Backtrack_stack.create ();
        undo_stack = Backtrack_stack.create ();
        stat_check = Stat.mk_int stat "simplex.check";
        stat_unsat = Stat.mk_int stat "simplex.conflicts";
        stat_define = Stat.mk_int stat "simplex.define";
        stat_propagate = Stat.mk_int stat "simplex.propagate";
        stat_vars = Stat.mk_int stat "simplex.n-vars";
      }
    in
    self

  type result = Sat of Subst.t | Unsat of unsat_cert

  let default_eps =
    let denom = 1 lsl 10 in
    Q.(one / of_int denom)

  (** Find an epsilon that is small enough for finding a solution, yet
      it must be positive.

      {!Erat.t} values are used to turn strict bounds ([X > 0]) into
      non-strict bounds ([X >= 0 + ε]), because the simplex algorithm
      only deals with non-strict bounds.
      When a solution is found, we need to turn {!Erat.t} into {!Q.t} by
      finding a rational value that is small enough that it will fit into
      all the intervals of [t]. This rational will be the actual value of [ε].
  *)
  let solve_epsilon (self : t) : Q.t =
    let eps =
      Iter.fold
        (fun eps x ->
          assert (Q.(eps >= zero));
          assert (Var_state.in_bounds_ x);

          let x_val = x.value in

          (*Log.debugf 50 (fun k->k "(@[solve-eps v.base=%a, v.eps=%a, emax=%a@])"
                            pp_q_dbg x_val.base pp_q_dbg x_val.eps_factor
                            pp_q_dbg eps);*)

          (* is lower bound *)
          let eps =
            match x.l_bound with
            | Some { b_val; _ }
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
                Q.(
                  (x_val.base - b_val.base)
                  / (b_val.eps_factor - x_val.eps_factor))
              in
              Q.min eps new_eps
            | _ -> eps
          in
          (* upper bound *)
          let eps =
            match x.u_bound with
            | Some { b_val; _ }
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
                Q.(
                  (b_val.base - x_val.base)
                  / (x_val.eps_factor - b_val.eps_factor))
              in
              Q.min eps new_eps
            | _ -> eps
          in
          eps)
        default_eps (Vec.to_iter self.vars)
    in
    if Q.(eps >= one) then
      Q.one
    else
      eps

  let model_ self : Subst.t =
    let eps = solve_epsilon self in
    Log.debugf 50 (fun k ->
        k "(@[simplex.model@ :epsilon-val %a@])" pp_q_dbg eps);
    let subst =
      Vec.to_iter self.vars
      |> Iter.fold
           (fun subst x ->
             let { base; eps_factor } = x.value in
             (* FIXME: if it's an int, pick an int value *)
             let v = Q.(base + (eps * eps_factor)) in
             V_map.add x.var v subst)
           V_map.empty
    in
    Log.debugf 10 (fun k -> k "(@[simplex.model@ %a@])" Subst.pp subst);
    subst

  let check ~on_propagate (self : t) : result =
    try
      check_exn ~on_propagate self;
      let m = model_ self in
      Sat m
    with E_unsat c -> Unsat c

  let check_branch_and_bound ~on_propagate:_ ~max_tree_nodes (self : t) :
      result option =
    Log.debugf 50 (fun k ->
        k "(@[simplex.branch-and-bound@ max-nodes %d@])" max_tree_nodes);
    if max_tree_nodes <= 0 then invalid_arg "simplex.check_branch_and_bound";
    let n = ref max_tree_nodes in

    let exception E_done in
    let cb_prop_ _ ~reason:_ = () in

    let is_valid_model (m : Subst.t) : (unit, var_state * Q.t) Result.t =
      let exception Found of var_state * Q.t in
      try
        Matrix.iter_rows self.matrix (fun _i x_i ->
            if x_i.is_int then (
              match Subst.eval m x_i.var with
              | Some n when not (Q.is_int n) ->
                (* found one! *)
                Log.debugf 10 (fun k ->
                    k "(@[simplex.int-var-assigned-to-non-int@ %a := %a@])"
                      Var_state.pp x_i Q.pp n);

                raise (Found (x_i, n))
              | _ -> ()
            ));
        Ok ()
      with Found (x, n) -> Error (x, n)
    in

    let rec loop (depth : int) : result =
      Log.debugf 30 (fun k ->
          k "(@[simplex.branch-and-bound.loop@ :depth %d@])" depth);
      if !n < 0 then raise E_done;

      decr n;
      match check ~on_propagate:cb_prop_ self with
      | Sat m as res ->
        (match is_valid_model m with
        | Ok () ->
          Log.debug 30 "(simplex.branch-and-bound.valid-model)";
          res
        | Error (x, val_x) ->
          Log.debugf 30 (fun k ->
              k
                "(@[simplex.branch-and-bound.invalid-int-model@ @[:var %a := \
                 %a@]@ :subst %a@])"
                Var_state.pp x Q.pp val_x Subst.pp m);

          assert x.is_int;
          let low = Q.floor val_x in
          let high = Z.(low + one) in
          Log.debugf 30 (fun k ->
              k "(@[simplex.branch-and-bound.cut@ :x %a@ :low %a@])"
                Var_state.pp x Z.pp low);
          (match
             ( loop_with (depth + 1) x.var `Leq (Q.of_bigint low),
               lazy (loop_with (depth + 1) x.var `Geq (Q.of_bigint high)) )
           with
          | (Sat _ as r), _ -> r
          | Unsat _, (lazy (Sat _ as r)) -> r
          | Unsat c1, (lazy (Unsat c2)) ->
            let cert =
              E_branch_and_bound
                { x; low; high; middle = val_x; pr_low = c1; pr_high = c2 }
            in
            Unsat cert))
      | Unsat _c as res ->
        Log.debug 30 "(simplex.branch-and-bound.unsat)";
        res
    (* loop, but asserting constraint [c] in addition *)
    and loop_with depth x op bnd : result =
      push_level self;
      let[@inline] cleanup () = pop_levels self 1 in

      try
        let c, lit =
          match op with
          | `Leq -> Constraint.leq x bnd, Arg.mk_lit x Op.Leq bnd
          | `Geq -> Constraint.geq x bnd, Arg.mk_lit x Op.Geq bnd
        in
        add_constraint self c lit ~on_propagate:cb_prop_;
        let r = loop depth in
        cleanup ();
        r
      with e ->
        cleanup ();
        raise e
    in
    try Some (loop 0) with E_done -> None

  let rec _check_cert (cert : unsat_cert) : unit =
    match cert with
    | E_bounds { x = _; lower; upper } ->
      (* unsat means [lower > upper] *)
      if not Erat.(lower.b_val > upper.b_val) then
        Error.errorf "invalid simplex cert: %a" Unsat_cert.pp cert
    | E_unsat_basic { x = _; x_bound; le; bounds } ->
      (* sum of [bounds], weighted by coefficient from [le] *)
      let is_lower, x_b =
        match x_bound with
        | (Leq | Lt), b -> false, b.b_val
        | (Geq | Gt), b -> true, b.b_val
      in
      let sum =
        List.fold_left
          (fun sum (c, x) ->
            match V_map.find x bounds with
            | exception Not_found ->
              Error.errorf "invalid simplex cert:@ %a@ var %a has no bound"
                Unsat_cert.pp cert V.pp x
            | Op.(Geq | Gt), _ when CCBool.equal is_lower Q.(c > zero) ->
              Error.errorf
                "invalid simplex cert:@ %a@ variable %a has coeff of the wrong \
                 sign %a"
                Unsat_cert.pp cert V.pp x pp_q_dbg c
            | Op.(Lt | Leq), _ when CCBool.equal is_lower Q.(c < zero) ->
              Error.errorf
                "invalid simplex cert:@ %a@ variable %a has coeff of the wrong \
                 sign %a"
                Unsat_cert.pp cert V.pp x pp_q_dbg c
            | _, b -> Erat.(sum + (c * b.b_val)))
          Erat.zero le
      in
      (* unsat if lower bound [x_b] is > [sum], which is an upper bound *)
      let ok =
        if is_lower then
          Erat.(x_b > sum)
        else
          Erat.(x_b < sum)
      in
      if not ok then
        Error.errorf "invalid simplex cert:@ %a@ sum of linexpr is %a"
          Unsat_cert.pp cert Erat.pp sum
    | E_branch_and_bound { pr_low; pr_high; _ } ->
      _check_cert pr_low;
      _check_cert pr_high
end
