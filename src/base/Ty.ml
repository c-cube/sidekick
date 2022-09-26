(** Core types *)

include Sidekick_core.Term
open Types_

let pp = pp_debug

type Const.view += Ty of ty_view
type data = Types_.data

let ops_ty =
  let pp out = function
    | Ty ty ->
      (match ty with
      | Ty_real -> Fmt.string out "Real"
      | Ty_int -> Fmt.string out "Int"
      | Ty_uninterpreted { id; _ } -> ID.pp out id)
    | _ -> ()
  in

  let equal a b =
    match a, b with
    | Ty a, Ty b ->
      (match a, b with
      | Ty_int, Ty_int | Ty_real, Ty_real -> true
      | Ty_uninterpreted u1, Ty_uninterpreted u2 -> ID.equal u1.id u2.id
      | (Ty_real | Ty_int | Ty_uninterpreted _), _ -> false)
    | _ -> false
  in

  let hash = function
    | Ty a ->
      (match a with
      | Ty_real -> Hash.int 2
      | Ty_int -> Hash.int 3
      | Ty_uninterpreted u -> Hash.combine2 10 (ID.hash u.id))
    | _ -> assert false
  in

  let ser _sink = function
    | Ty a ->
      Ser_value.(
        (match a with
        | Ty_real -> "ty.Real", null
        | Ty_int -> "ty.Int", null
        | Ty_uninterpreted { id; finite } ->
          "ty.id", dict_of_list [ "id", ID.ser id; "fin", bool finite ]))
    | _ -> assert false
  in
  { Const.Ops.pp; equal; hash; ser }

let const_decoders : Const.decoders =
 fun _tst ->
  [
    ("ty.Real", ops_ty, Ser_decode.(fun _ -> return @@ Ty Ty_real));
    ("ty.Int", ops_ty, Ser_decode.(fun _ -> return @@ Ty Ty_int));
    ( "ty.id",
      ops_ty,
      Ser_decode.(
        fun _ ->
          let+ id = dict_field "id" ID.deser
          and+ finite = dict_field "fin" bool in
          Ty (Ty_uninterpreted { id; finite })) );
  ]

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

let uninterpreted_str tst s : t = uninterpreted tst (ID.make s)

let is_uninterpreted (self : t) =
  match view self with
  | E_const { Const.c_view = Ty (Ty_uninterpreted _); _ } -> true
  | _ -> false
