open! Sidekick_base

type t = { fun_symbols: unit Term.Tbl.t; ty_symbols: unit Term.Tbl.t }

let create () : t =
  { fun_symbols = Term.Tbl.create 32; ty_symbols = Term.Tbl.create 32 }

let add_ty (self : t) ty_const : unit = Term.Tbl.add self.ty_symbols ty_const ()
let add_fun (self : t) const : unit = Term.Tbl.add self.fun_symbols const ()

let build (self : t) (sat : Solver.sat_result) : Model.t =
  let m = ref Model.empty in

  (* process [t], whose value is [value] in the model *)
  let examine_term t ~value : unit =
    let f, args = Term.unfold_app t in

    (* TODO: types *)
    if Term.Tbl.mem self.fun_symbols f then (
      (* add entry for [f], to build a if-then-else tree *)
      match List.map (fun t -> sat.get_value t |> Option.get) args with
      | exception _ ->
        Log.debugf 1 (fun k ->
            k "(@[build-model.warn@ :no-entry-for %a@])" Term.pp t)
      | v_args ->
        (* see if [v_args] already maps to a value *)
        let other_v = Model.get_fun_entry f v_args !m in
        Option.iter
          (fun v' ->
            if not (Term.equal value v') then
              Error.errorf
                "Inconsistent model@ for fun `%a`,@ values %a@ map to `%a` and \
                 `%a`"
                Term.pp f (Fmt.Dump.list Term.pp) v_args Term.pp value Term.pp
                v')
          other_v;
        (* save mapping *)
        m := Model.add_fun_entry f v_args value !m
    )
  in

  sat.iter_classes (fun (cls, v) -> cls (fun t -> examine_term t ~value:v));

  !m
