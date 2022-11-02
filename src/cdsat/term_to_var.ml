type t = { vst: TVar.store; mutable hooks: hook list }
and hook = t -> Term.t -> TVar.theory_view option

let create vst : t = { vst; hooks = [] }
let add_hook self h = self.hooks <- h :: self.hooks

let rec convert (self : t) (t : Term.t) : TVar.t =
  let rec try_hooks = function
    | [] ->
      (* no hook worked *)
      Error.errorf "cdsat.term-to-var: no hook accepted term `%a`"
        (Term.pp_limit ~max_depth:5 ~max_nodes:30)
        t
    | h :: tl_h ->
      (match h self t with
      | Some theory_view ->
        let v = TVar.Internal.create self.vst t ~theory_view in
        v
      | None -> try_hooks tl_h)
  in

  match TVar.get_of_term self.vst t with
  | Some v -> v
  | None -> try_hooks self.hooks
