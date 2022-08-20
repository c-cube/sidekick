open Types_

type t = e_node

let[@inline] equal (n1 : t) n2 = n1 == n2
let[@inline] hash n = Term.hash n.n_term
let[@inline] term n = n.n_term
let[@inline] pp out n = Term.pp_debug out n.n_term
let[@inline] as_lit n = n.n_as_lit

let make (t : Term.t) : t =
  let rec n =
    {
      n_term = t;
      n_sig0 = None;
      n_bits = Bits.empty;
      n_parents = Bag.empty;
      n_as_lit = None;
      (* TODO: provide a method to do it *)
      n_root = n;
      n_expl = FL_none;
      n_next = n;
      n_size = 1;
    }
  in
  n

let[@inline] is_root (n : e_node) : bool = n.n_root == n

(* traverse the equivalence class of [n] *)
let iter_class_ (n_start : e_node) : e_node Iter.t =
 fun yield ->
  let rec aux u =
    yield u;
    if u.n_next != n_start then aux u.n_next
  in
  aux n_start

let[@inline] iter_class n = iter_class_ n

let[@inline] iter_parents (n : e_node) : e_node Iter.t =
  assert (is_root n);
  Bag.to_iter n.n_parents

module Internal_ = struct
  let iter_class_ = iter_class_
  let make = make
end
