open Sidekick_core_logic
module Tr = Sidekick_trace
module T = Term

type term_ref = Tr.entry_id

type Tr.entry_view +=
  | T_ty of int
  | T_app of term_ref * term_ref
  | T_var of string * term_ref
  | T_bvar of int * term_ref
  | T_const of { c: Const.view; c_ops: Const.Ops.t; ty: term_ref }
  | T_lam of { v_name: string; v_ty: term_ref; body: term_ref }
  | T_pi of { v_name: string; v_ty: term_ref; body: term_ref }
  (* FIXME: remove when we decode *)
  [@@ocaml.warning "-38"]

type state = { sink: Tr.Sink.t; emitted: Tr.Entry_id.t T.Weak_map.t }

let emit_term_ (self : state) (t : Term.t) =
  let module V = Ser_value in
  let rec loop t =
    match T.Weak_map.find_opt self.emitted t with
    | Some id -> id
    | None ->
      let loop' t = V.int (loop t :> int) in
      let tag, v =
        match T.view t with
        | T.E_var v -> "TV", V.(list [ string (Var.name v); loop' v.v_ty ])
        | T.E_bound_var v -> "Tv", V.(list [ int (Bvar.idx v); loop' v.bv_ty ])
        | T.E_app (f, a) -> "T@", V.(list [ loop' f; loop' a ])
        | T.E_type i -> "Ty", V.int i
        | T.E_const ({ Const.c_ty; _ } as const) ->
          let tag, view = Const.ser ~ser_t:loop' const in
          ( "Tc",
            let fields =
              (if V.is_null view then
                []
              else
                [ "v", view ])
              @ [ "ty", loop' c_ty; "tag", V.string tag ]
            in
            V.dict_of_list fields )
        | T.E_app_fold { f; args; acc0 } ->
          "Tf@", V.(list [ loop' f; list (List.map loop' args); loop' acc0 ])
        | T.E_lam (name, ty, bod) ->
          "Tl", V.(list [ string name; loop' ty; loop' bod ])
        | T.E_pi (name, ty, bod) ->
          "Tp", V.(list [ string name; loop' ty; loop' bod ])
      in

      let id = Tr.Sink.emit self.sink ~tag v in
      T.Weak_map.add self.emitted t id;
      id
  in
  loop t

class type t =
  object
    method emit_term : Term.t -> term_ref
  end

class dummy : t =
  object
    method emit_term _ = Tr.Entry_id.dummy
  end

(* tracer *)
class concrete ~sink : t =
  object
    val state = { sink; emitted = T.Weak_map.create 16 }
    method emit_term (t : Term.t) : term_ref = emit_term_ state t
  end

let create ~sink () : t = new concrete ~sink
let emit (self : #t) (t : T.t) : term_ref = self#emit_term t
let emit' self t : unit = ignore (emit self t : term_ref)
