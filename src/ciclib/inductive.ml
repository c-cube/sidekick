module T = Term

type cstor = Types_.cstor = { c_name: string; c_ty: T.t }

type spec = Types_.spec = {
  name: string;
  univ_params: Level.var list;
  n_params: int;
  ty: T.t;
  cstors: cstor list;
}
(** Inductive spec *)

let pp_cstor out (c : cstor) : unit =
  Fmt.fprintf out "(@[%s : %a@])" c.c_name T.pp_debug c.c_ty

let pp_spec out (self : spec) : unit =
  Fmt.fprintf out "@[<2>@[%s %a@]:@ %a [%d params] :=@ %a@]" self.name
    Fmt.Dump.(list string)
    self.univ_params T.pp_debug self.ty self.n_params
    Fmt.(hvbox @@ Dump.(list pp_cstor))
    self.cstors

let cstor_is_valid (spec : spec) (self : cstor) : bool =
  let rec loop (ty : T.t) : bool =
    let hd, _args = T.unfold_app ty in
    match T.view hd with
    | T.E_const (c, _) when c.c_name = spec.name ->
      (* TODO: check that [ty] is correct *)
      true
    | _ -> assert false (* TODO: handle recursive cases *)
  in
  loop self.c_ty

let is_valid self = List.for_all (cstor_is_valid self) self.cstors
