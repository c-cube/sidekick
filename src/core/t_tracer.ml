open Sidekick_core_logic
module Tr = Sidekick_trace
module T = Term

type term_ref = Tr.entry_id
type const_ref = Tr.entry_id

type Tr.entry_view +=
  | T_ty of int
  | T_app of term_ref * term_ref
  | T_var of string * term_ref
  | T_bvar of int * term_ref
  | T_const of { c: Const.view; c_ops: Const.ops; ty: term_ref }
  | T_lam of { v_name: string; v_ty: term_ref; body: term_ref }
  | T_pi of { v_name: string; v_ty: term_ref; body: term_ref }

(* tracer *)
type t = { sink: Tr.Sink.t; emitted: Tr.Entry_id.t T.Weak_map.t }

let create ~sink () : t = { sink; emitted = T.Weak_map.create 16 }

let emit (self : t) (t : T.t) : Tr.Entry_id.t =
  let module V = Ser_value in
  let rec loop t =
    match T.Weak_map.find_opt self.emitted t with
    | Some id -> id
    | None ->
      let tag, v =
        match T.view t with
        | T.E_var v ->
          let ty = loop (Var.ty v) in
          "TV", V.(list [ string (Var.name v); int (ty :> int) ])
        | _ -> assert false
      in

      let id = Tr.Sink.emit self.sink ~tag v in
      T.Weak_map.add self.emitted t id;
      id
  in
  loop t
