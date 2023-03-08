open Types_
module T = Term
module Str_map = Util.Str_map

module Env = struct
  type t = {
    consts: T.t Str_map.t;
    inductives: Inductive.spec Str_map.t;
    cstors: Inductive.cstor Str_map.t;
  }

  let pp_str_map ppx out (m : _ Str_map.t) =
    Fmt.iter Fmt.Dump.(pair string ppx) out (Str_map.to_iter m)

  let pp out (self : t) =
    let { consts; inductives; cstors } = self in
    Fmt.fprintf out "{ @[consts=%a;@ inductives=%a;@ cstors=%a@] }"
      (pp_str_map T.pp_debug) consts
      (pp_str_map Inductive.pp_spec)
      inductives
      (pp_str_map Inductive.pp_cstor)
      cstors

  let empty : t =
    {
      consts = Str_map.empty;
      inductives = Str_map.empty;
      cstors = Str_map.empty;
    }

  let add_def (self : t) name rhs : t =
    { self with consts = Str_map.add name rhs self.consts }

  let add_inductive (self : t) (ind : Inductive.spec) : t =
    {
      self with
      inductives = Str_map.add ind.name ind self.inductives;
      cstors =
        List.fold_left
          (fun cstors c -> Str_map.add c.c_name c cstors)
          self.cstors ind.cstors;
    }
end

module Stack = struct
  type t = T.t list

  let empty = []
  let push t l : t = t :: l
  let pp = Fmt.Dump.(list T.pp_debug)
end

let ty_check (env : Env.t) (st : Stack.t) (self : T.t) : T.t =
  let rec loop (st : Stack.t) (self : T.t) : T.t =
    match T.view self with
    | E_type l -> T.type_of_univ (Level.succ l)
    | E_bound_var v ->
      (match List.nth st v.bv_idx with
      | exception _ ->
        Error.errorf "bound variable %a is not bound in env %a" Bvar.pp v
          Stack.pp st
      | ty -> ty)
    | E_const (c, args) -> assert false (* TODO: check definition? *)
    | E_app (_, _) | E_lam (_, _, _, _) | E_pi (_, _, _, _) ->
      assert false (* TODO: *)
  in
  loop st self
