open Sidekick_core_logic

type term = Term.t
type ty = Term.t

type Const.view +=
  | Fresh of {
      id: int;  (** Id of this constant *)
      gensym_id: int;  (** Id of the gensym *)
      pre: string;  (** Printing prefix *)
      ty: ty;
    }

let ops =
  let equal a b =
    match a, b with
    | Fresh a, Fresh b -> a.id = b.id && a.gensym_id = b.gensym_id
    | _ -> false
  in

  let hash = function
    | Fresh { id; gensym_id; _ } ->
      Hash.combine3 15232 (Hash.int id) (Hash.int gensym_id)
    | _ -> assert false
  in

  let pp out = function
    | Fresh { id; pre; _ } -> Fmt.fprintf out "$%s[%d]" pre id
    | _ -> assert false
  in

  let ser ser_t = function
    | Fresh { id; pre; ty; _ } ->
      "gensym", Ser_value.(list [ int id; string pre; ser_t ty ])
    | _ -> assert false
  in
  { Const.Ops.equal; hash; pp; ser }

type t = { tst: Term.store; self_id: int; mutable fresh: int }

(* TODO: use atomic *)
let id_ = ref 0

let create tst : t =
  let self_id = !id_ in
  incr id_;
  { tst; self_id; fresh = 0 }

let reset self = self.fresh <- 0

let fresh_term (self : t) ~pre (ty : ty) : Term.t =
  let id = self.fresh in
  self.fresh <- 1 + self.fresh;
  let c =
    Term.const self.tst
    @@ Const.make (Fresh { id; gensym_id = self.self_id; pre; ty }) ops ~ty
  in
  c
