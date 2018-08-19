
open Solver_types

type t = equiv_class
type payload = equiv_class_payload = ..

let field_is_active = Node_bits.mk_field()
let field_is_pending = Node_bits.mk_field()
let field_is_literal = Node_bits.mk_field()
let () = Node_bits.freeze()

let[@inline] equal (n1:t) n2 = n1==n2
let[@inline] hash n = Term.hash n.n_term
let[@inline] term n = n.n_term
let[@inline] payload n = n.n_payload
let[@inline] pp out n = Term.pp out n.n_term

let make (t:term) : t =
  let rec n = {
    n_term=t;
    n_bits=Node_bits.empty;
    n_parents=Bag.empty;
    n_root=n;
    n_expl=E_none;
    n_payload=[];
    n_next=n;
    n_size=1;
    n_tags=Util.Int_map.empty;
  } in
  n

let set_payload ?(can_erase=fun _->false) n e =
  let rec aux = function
    | [] -> [e]
    | e' :: tail when can_erase e' -> e :: tail
    | e' :: tail -> e' :: aux tail
  in
  n.n_payload <- aux n.n_payload

let payload_find ~f:p n =
  begin match n.n_payload with
    | [] -> None
    | e1 :: tail ->
      match p e1, tail with
        | Some _ as res, _ -> res
        | None, [] -> None
        | None, e2 :: tail2 ->
          match p e2, tail2 with
            | Some _ as res, _ -> res
            | None, [] -> None
            | None, e3 :: tail3 ->
              match p e3 with
                | Some _ as res -> res
                | None -> CCList.find_map p tail3
  end

let payload_pred ~f:p n =
  begin match n.n_payload with
    | [] -> false
    | e :: _ when p e -> true
    | _ :: e :: _ when p e -> true
    | _ :: _ :: e :: _ when p e -> true
    | l -> List.exists p l
  end

let[@inline] get_field f t = Node_bits.get f t.n_bits
let[@inline] set_field f b t = t.n_bits <- Node_bits.set f b t.n_bits

module Tbl = CCHashtbl.Make(struct
    type t = equiv_class
    let equal = equal
    let hash = hash
  end)

let dummy = make Term.dummy
