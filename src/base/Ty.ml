(** Core types *)

include Sidekick_core.Term
open Types_

let pp = pp_debug

type Const.view += Ty of ty_view
type data = Types_.data

let ops_ty : Const.ops =
  (module struct
    let pp out = function
      | Ty ty ->
        (match ty with
        | Ty_real -> Fmt.string out "Real"
        | Ty_int -> Fmt.string out "Int"
        | Ty_uninterpreted { id; _ } -> ID.pp out id)
      | _ -> ()

    let equal a b =
      match a, b with
      | Ty a, Ty b ->
        (match a, b with
        | Ty_int, Ty_int | Ty_real, Ty_real -> true
        | Ty_uninterpreted u1, Ty_uninterpreted u2 -> ID.equal u1.id u2.id
        | (Ty_real | Ty_int | Ty_uninterpreted _), _ -> false)
      | _ -> false

    let hash = function
      | Ty a ->
        (match a with
        | Ty_real -> Hash.int 2
        | Ty_int -> Hash.int 3
        | Ty_uninterpreted u -> Hash.combine2 10 (ID.hash u.id))
      | _ -> assert false
  end)

open struct
  let mk_ty0 tst view =
    let ty = Term.type_ tst in
    Term.const tst @@ Const.make (Ty view) ops_ty ~ty
end
(* TODO: handle polymorphic constants *)

let int tst : ty = mk_ty0 tst Ty_int
let real tst : ty = mk_ty0 tst Ty_real

let is_real t =
  match Term.view t with
  | E_const { Const.c_view = Ty Ty_real; _ } -> true
  | _ -> false

let is_int t =
  match Term.view t with
  | E_const { Const.c_view = Ty Ty_int; _ } -> true
  | _ -> false

let uninterpreted tst id : t =
  mk_ty0 tst (Ty_uninterpreted { id; finite = false })

let is_uninterpreted (self : t) =
  match view self with
  | E_const { Const.c_view = Ty (Ty_uninterpreted _); _ } -> true
  | _ -> false
