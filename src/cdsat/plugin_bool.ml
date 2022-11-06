type 'a view = 'a Bool_view.t

(** Argument to the plugin *)
module type ARG = sig
  val view : Term.t -> Term.t view
  val or_l : Term.store -> Term.t list -> Term.t
  val and_l : Term.store -> Term.t list -> Term.t
end

(* our custom view of terms *)
type TVar.theory_view +=
  | T_bool of bool
  | T_and of TLit.t array
  | T_or of TLit.t array

(* our internal state *)
type t = { arg: (module ARG); tst: Term.store; vst: TVar.store }

let push_level (self : t) = ()
let pop_levels (self : t) n = ()

let decide (self : t) (v : TVar.t) : Value.t option =
  match TVar.theory_view self.vst v with
  | T_bool b ->
    (* FIXME: this should be propagated earlier, shouldn't it? *)
    Some (Term.bool_val self.tst b)
  | T_and _ | T_or _ ->
    (* TODO: phase saving? or is it done directly in the core? *)
    Some (Term.true_ self.tst)
  | _ when Term.has_ty_bool (TVar.term self.vst v) ->
    (* TODO: phase saving? or is it done directly in the core? *)
    Some (Term.true_ self.tst)
  | _ -> None

let propagate (self : t) (act : Core.Plugin_action.t) (v : TVar.t)
    (value : Value.t) : unit =
  Log.debugf 0 (fun k ->
      k "(@[bool-plugin.propagate %a@])" (TVar.pp self.vst) v);
  ()
(* TODO: BCP *)

let term_to_var_hooks (self : t) : _ list =
  let (module A) = self.arg in

  let rec to_tlit t2v (t : Term.t) : TLit.t =
    match A.view t with
    | Bool_view.B_not u ->
      let lit = to_tlit t2v u in
      TLit.neg lit
    | _ ->
      let v = Term_to_var.convert t2v t in
      TLit.make true v
  in

  (* main hook to convert formulas *)
  let h t2v (t : Term.t) : _ option =
    match A.view t with
    | Bool_view.B_bool b -> Some (T_bool b)
    | Bool_view.B_and l ->
      let lits = Util.array_of_list_map (to_tlit t2v) l in
      Some (T_and lits)
    | Bool_view.B_or l ->
      let lits = Util.array_of_list_map (to_tlit t2v) l in
      Some (T_or lits)
    | _ -> None
  in
  [ h ]

let builder ((module A : ARG) as arg) : Core.Plugin.builder =
  let create vst : t =
    let tst = TVar.Store.tst vst in
    { arg; vst; tst }
  in
  Core.Plugin.make_builder ~name:"bool" ~create ~push_level ~pop_levels ~decide
    ~propagate ~term_to_var_hooks ()
