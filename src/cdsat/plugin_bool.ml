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

type Core.Plugin.event += Eval of TVar.t | BCP of TVar.t

(* create watch *)
let on_add_var (self : t) acts (v : TVar.t) : unit =
  match TVar.theory_view self.vst v with
  | T_and lits | T_or lits ->
    let vars_of_lits = Util.array_to_list_map TLit.var lits in
    Core.Plugin_action.watch1 acts vars_of_lits (Eval v);
    Core.Plugin_action.watch2 acts (v :: vars_of_lits) (BCP v)
  | _ -> ()

let on_event (self : t) acts ~unit (ev : Core.Plugin.event) : unit =
  match ev with
  | Eval v ->
    (* TODO: evaluate [v] *)
    Log.debugf 1 (fun k -> k "(@[cdsat.bool.eval@ %a@])" (TVar.pp self.vst) v)
  | BCP v ->
    (* TODO: check if we can eval *)
    Log.debugf 1 (fun k -> k "(@[cdsat.bool.bcp@ %a@])" (TVar.pp self.vst) v)
  | _ -> ()

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

let iter_theory_view _ (v : TVar.theory_view) k =
  match v with
  | T_and lits | T_or lits -> Array.iter (fun { TLit.var; _ } -> k var) lits
  | _ -> ()

let builder ((module A : ARG) as arg) : Core.Plugin.builder =
  let create vst : t =
    let tst = TVar.Store.tst vst in
    { arg; vst; tst }
  in
  Core.Plugin.make_builder ~name:"bool" ~create ~push_level ~pop_levels
    ~iter_theory_view ~decide ~on_add_var ~on_event ~term_to_var_hooks ()
