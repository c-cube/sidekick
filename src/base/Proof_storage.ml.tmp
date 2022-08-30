open Base_types

(* we store steps as binary chunks *)
module CS = Chunk_stack
module PS = Proof_ser

module Config = struct
  type storage = No_store | In_memory | On_disk_at of string

  let pp_storage out = function
    | No_store -> Fmt.string out "no-store"
    | In_memory -> Fmt.string out "in-memory"
    | On_disk_at file -> Fmt.fprintf out "(on-file :at %S)" file

  type t = { enabled: bool; storage: storage }

  let default = { enabled = true; storage = In_memory }
  let empty = { enabled = false; storage = No_store }

  let pp out (self : t) =
    let { enabled; storage } = self in
    Fmt.fprintf out "(@[config@ :enabled %B@ :storage %a@])" enabled pp_storage
      storage

  let enable b self = { self with enabled = b }
  let store_in_memory self = { self with storage = In_memory }
  let store_on_disk_at file self = { self with storage = On_disk_at file }
  let no_store self = { self with storage = No_store }
end

(* a step is just a unique integer ID.
   The actual step is stored in the chunk_stack. *)
type step_id = Proof_ser.ID.t
type term_id = Proof_ser.ID.t
type lit = Lit.t
type term = Term.t

module Step_vec = struct
  type elt = step_id
  type t = elt Vec.t

  let get = Vec.get
  let size = Vec.size
  let iter = Vec.iter
  let iteri = Vec.iteri
  let create ?cap:_ () = Vec.create ()
  let clear = Vec.clear
  let copy = Vec.copy
  let is_empty = Vec.is_empty
  let push = Vec.push
  let fast_remove = Vec.fast_remove
  let filter_in_place = Vec.filter_in_place
  let ensure_size v len = Vec.ensure_size v ~elt:0l len
  let pop = Vec.pop_exn
  let set = Vec.set
  let shrink = Vec.shrink
  let to_iter = Vec.to_iter
end

type t = {
  mutable enabled: bool;
  buf: Buffer.t;
  out: Proof_ser.Bare.Encode.t;
  mutable storage: Storage.t;
  dispose: unit -> unit;
  mutable steps_writer: CS.Writer.t;
  mutable next_id: int;
  map_term: term_id Term.Tbl.t; (* term -> proof ID *)
  map_fun: term_id Fun.Tbl.t;
}

let disable (self : t) : unit =
  self.enabled <- false;
  self.storage <- Storage.No_store;
  self.dispose ();
  self.steps_writer <- CS.Writer.dummy;
  ()

let nop_ _ = ()

let create ?(config = Config.default) () : t =
  (* acquire resources for logging *)
  let storage, steps_writer, dispose =
    match config.Config.storage with
    | Config.No_store -> Storage.No_store, CS.Writer.dummy, nop_
    | Config.In_memory ->
      let buf = CS.Buf.create ~cap:256 () in
      Storage.In_memory buf, CS.Writer.into_buf buf, nop_
    | Config.On_disk_at file ->
      let oc =
        open_out_gen
          [ Open_creat; Open_wronly; Open_trunc; Open_binary ]
          0o644 file
      in
      let w = CS.Writer.into_channel oc in
      let dispose () = close_out oc in
      Storage.On_disk (file, oc), w, dispose
  in
  let buf = Buffer.create 1_024 in
  let out = Proof_ser.Bare.Encode.of_buffer buf in
  {
    enabled = config.Config.enabled;
    next_id = 1;
    buf;
    out;
    map_term = Term.Tbl.create 32;
    map_fun = Fun.Tbl.create 32;
    steps_writer;
    storage;
    dispose;
  }

let empty = create ~config:Config.empty ()
let iter_steps_backward (self : t) = Storage.iter_steps_backward self.storage
let dummy_step : step_id = Int32.min_int
let[@inline] enabled (self : t) = self.enabled

(* allocate a unique ID to refer to an event in the trace *)
let[@inline] alloc_id (self : t) : Proof_ser.ID.t =
  let n = self.next_id in
  self.next_id <- 1 + self.next_id;
  Int32.of_int n

(* emit a proof step *)
let emit_step_ (self : t) (step : Proof_ser.Step.t) : unit =
  if enabled self then (
    Buffer.clear self.buf;
    Proof_ser.Step.encode self.out step;
    Chunk_stack.Writer.add_buffer self.steps_writer self.buf
  )

let emit_fun_ (self : t) (f : Fun.t) : term_id =
  try Fun.Tbl.find self.map_fun f
  with Not_found ->
    let id = alloc_id self in
    Fun.Tbl.add self.map_fun f id;
    let f_name = ID.to_string (Fun.id f) in
    emit_step_ self
      Proof_ser.{ Step.id; view = Fun_decl { Fun_decl.f = f_name } };
    id

let rec emit_term_ (self : t) (t : Term.t) : term_id =
  try Term.Tbl.find self.map_term t
  with Not_found ->
    let view =
      match Term_cell.map (emit_term_ self) @@ Term.view t with
      | Term_cell.Bool b -> PS.Step_view.Expr_bool { PS.Expr_bool.b }
      | Term_cell.Ite (a, b, c) ->
        PS.Step_view.Expr_if { PS.Expr_if.cond = a; then_ = b; else_ = c }
      | Term_cell.Not a -> PS.Step_view.Expr_not { PS.Expr_not.f = a }
      | Term_cell.App_fun ({ fun_view = Fun.Fun_is_a c; _ }, args) ->
        assert (CCArray.length args = 1);
        let c = emit_fun_ self (Fun.cstor c) in
        let arg = CCArray.get args 0 in
        PS.Step_view.Expr_isa { PS.Expr_isa.c; arg }
      | Term_cell.App_fun (f, arr) ->
        let f = emit_fun_ self f in
        PS.Step_view.Expr_app
          { PS.Expr_app.f; args = (arr : _ array :> _ array) }
      | Term_cell.Eq (a, b) ->
        PS.Step_view.Expr_eq { PS.Expr_eq.lhs = a; rhs = b }
      | LRA _ | LIA _ -> assert false
      (* TODO *)
    in

    let id = alloc_id self in
    Term.Tbl.add self.map_term t id;
    emit_step_ self { id; view };
    id

let emit_lit_ (self : t) (lit : Lit.t) : term_id =
  let sign = Lit.sign lit in
  let t = emit_term_ self (Lit.term lit) in
  if sign then
    t
  else
    Int32.neg t

let emit_no_return_ (self : t) f : unit =
  if enabled self then (
    let view = f () in
    emit_step_ self { PS.Step.id = -1l; view }
  )

let emit_unsat c (self : t) : unit =
  emit_no_return_ self @@ fun () -> PS.(Step_view.Step_unsat { Step_unsat.c })

(** What a rule can return. It can return an existing step, or ask to create
    a new one. *)
type rule_res = R_new of PS.Step_view.t | R_old of step_id

type rule = t -> rule_res

let emit_rule_ (self : t) (f : rule) : step_id =
  if enabled self then (
    match f self with
    | R_old id -> id
    | R_new view ->
      let id = alloc_id self in
      emit_step_ self { PS.Step.id; view };
      id
  ) else
    dummy_step

module Proof_trace = struct
  module A = struct
    type nonrec step_id = step_id
    type nonrec rule = rule

    module Step_vec = Step_vec
  end

  type nonrec t = t

  let enabled = enabled
  let add_step = emit_rule_
  let[@inline] add_unsat self id = emit_unsat id self
  let delete _ _ = ()
end

let r_new v = R_new v
let r_old id = R_old id

module Rule_sat = struct
  type nonrec lit = lit
  type nonrec step_id = step_id
  type nonrec rule = rule

  let sat_redundant_clause lits ~hyps : rule =
   fun self ->
    let lits = Iter.map (emit_lit_ self) lits |> Iter.to_array in
    let clause = Proof_ser.{ Clause.lits } in
    let hyps = Iter.to_array hyps in
    r_new @@ PS.Step_view.Step_rup { res = clause; hyps }

  let sat_input_clause (lits : Lit.t Iter.t) : rule =
   fun self ->
    let lits = Iter.map (emit_lit_ self) lits |> Iter.to_array in
    r_new @@ PS.(Step_view.Step_input { Step_input.c = { Clause.lits } })

  (* TODO *)
  let sat_unsat_core _ (_pr : t) = r_old dummy_step
end

module Rule_core = struct
  type nonrec term = term
  type nonrec step_id = step_id
  type nonrec rule = rule
  type nonrec lit = lit

  let sat_redundant_clause lits ~hyps : rule =
   fun self ->
    let lits = Iter.map (emit_lit_ self) lits |> Iter.to_array in
    let clause = Proof_ser.{ Clause.lits } in
    let hyps = Iter.to_array hyps in
    r_new @@ PS.Step_view.Step_rup { res = clause; hyps }

  let define_term t u : rule =
   fun self ->
    let t = emit_term_ self t and u = emit_term_ self u in
    r_new @@ PS.(Step_view.Expr_def { Expr_def.c = t; rhs = u })

  let proof_p1 rw_with c : rule =
   fun _self ->
    r_new @@ PS.(Step_view.Step_proof_p1 { Step_proof_p1.c; rw_with })

  let proof_r1 unit c : rule =
   fun _self -> r_new @@ PS.(Step_view.Step_proof_r1 { Step_proof_r1.c; unit })

  let proof_res ~pivot c1 c2 : rule =
   fun self ->
    let pivot = emit_term_ self pivot in
    r_new @@ PS.(Step_view.Step_proof_res { Step_proof_res.c1; c2; pivot })

  let lemma_preprocess t u ~using : rule =
   fun self ->
    let t = emit_term_ self t and u = emit_term_ self u in
    let using = using |> Iter.to_array in
    r_new @@ PS.(Step_view.Step_preprocess { Step_preprocess.t; u; using })

  let lemma_true t : rule =
   fun self ->
    let t = emit_term_ self t in
    r_new @@ PS.(Step_view.Step_true { Step_true.true_ = t })

  let lemma_cc lits : rule =
   fun self ->
    let lits = Iter.map (emit_lit_ self) lits |> Iter.to_array in
    r_new @@ PS.(Step_view.Step_cc { Step_cc.eqns = lits })

  let lemma_rw_clause c ~res ~using : rule =
   fun self ->
    let using = Iter.to_array using in
    if Array.length using = 0 then
      r_old c
    (* useless step *)
    else (
      let lits = Iter.map (emit_lit_ self) res |> Iter.to_array in
      let res = Proof_ser.{ Clause.lits } in
      r_new @@ PS.(Step_view.Step_clause_rw { Step_clause_rw.c; res; using })
    )

  (* TODO *)
  let with_defs _ _ (_pr : t) = r_old dummy_step
end

(* not useful *)
let del_clause _ _ (_pr : t) = ()

module Rule_bool = struct
  type nonrec term = term
  type nonrec lit = lit
  type nonrec rule = rule

  let lemma_bool_tauto lits : rule =
   fun self ->
    let lits = Iter.map (emit_lit_ self) lits |> Iter.to_array in
    r_new @@ PS.(Step_view.Step_bool_tauto { Step_bool_tauto.lits })

  let lemma_bool_c rule (ts : Term.t list) : rule =
   fun self ->
    let exprs = Util.array_of_list_map (emit_term_ self) ts in
    r_new @@ PS.(Step_view.Step_bool_c { Step_bool_c.exprs; rule })

  let lemma_bool_equiv _ _ _ = r_old dummy_step
  let lemma_ite_true ~ite:_ _ = r_old dummy_step
  let lemma_ite_false ~ite:_ _ = r_old dummy_step
end

(* TODO *)

let lemma_lra _ _ = r_old dummy_step
let lemma_relax_to_lra _ _ = r_old dummy_step
let lemma_lia _ _ = r_old dummy_step

module Rule_data = struct
  type nonrec lit = lit
  type nonrec rule = rule
  type nonrec term = term

  let lemma_isa_cstor ~cstor_t:_ _ (_pr : t) = r_old dummy_step
  let lemma_select_cstor ~cstor_t:_ _ (_pr : t) = r_old dummy_step
  let lemma_isa_split _ _ (_pr : t) = r_old dummy_step
  let lemma_isa_sel _ (_pr : t) = r_old dummy_step
  let lemma_isa_disj _ _ (_pr : t) = r_old dummy_step
  let lemma_cstor_inj _ _ _ (_pr : t) = r_old dummy_step
  let lemma_cstor_distinct _ _ (_pr : t) = r_old dummy_step
  let lemma_acyclicity _ (_pr : t) = r_old dummy_step
end

module Unsafe_ = struct
  let[@inline] id_of_proof_step_ (p : step_id) : step_id = p
end
