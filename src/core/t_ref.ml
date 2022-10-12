(** Term reference *)

open Sidekick_core_logic

open struct
  module Tr = Sidekick_trace
end

type t = Tr.entry_id
type Const.view += Ref of t

let ops : Const.Ops.t =
  let pp out = function
    | Ref x -> Fmt.fprintf out "(@[ref %a@])" Tr.Entry_id.pp x
    | _ -> assert false
  in

  let equal a b =
    match a, b with
    | Ref a, Ref b -> Tr.Entry_id.equal a b
    | _ -> false
  in
  let hash = function
    | Ref a -> Hash.combine2 519 (Tr.Entry_id.hash a)
    | _ -> assert false
  in

  let ser _sink = function
    | Ref a -> "!", Ser_value.(int a)
    | _ -> assert false
  in
  { Const.Ops.equal; pp; hash; ser }

let ref (tst : Term.store) (r : t) ~ty : Term.t =
  Term.const tst @@ Const.make (Ref r) ops ~ty

let[@inline] as_ref t : t option =
  match Term.view t with
  | Term.E_const { Const.c_view = Ref r; _ } -> Some r
  | _ -> None

let const_decoders : Const.decoders =
  [
    ( "!",
      ops,
      Ser_decode.(
        fun _dec_term ->
          let+ i = int in
          Ref i) );
  ]
