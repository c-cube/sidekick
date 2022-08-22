open Sidekick_core
module T = Term
module T_tbl = Term.Tbl

type node = {
  mutable n_next: node; (* next in class *)
  mutable n_size: int; (* size of class *)
}

module Node = struct
  type t = node

  let[@inline] equal (n1 : t) n2 = n1 == n2
  let[@inline] size (n : t) = n.n_size
  let[@inline] is_root n = n == n.n_next

  let[@unroll 2] rec root n =
    if n.n_next == n then
      n
    else (
      let r = root n.n_next in
      n.n_next <- r;
      r
    )

  let make () : t =
    let rec n = { n_size = 1; n_next = n } in
    n
end

type t = { tbl: node T_tbl.t }

let create () : t = { tbl = T_tbl.create 8 }
let clear (self : t) : unit = T_tbl.clear self.tbl

let add_ (self : t) (t : T.t) : node =
  try T_tbl.find self.tbl t
  with Not_found ->
    let n = Node.make () in
    T_tbl.add self.tbl t n;
    n

let merge (self : t) (t1 : T.t) (t2 : T.t) =
  let n1 = add_ self t1 |> Node.root in
  let n2 = add_ self t2 |> Node.root in
  if n1 != n2 then (
    let n1, n2 =
      if Node.size n1 > Node.size n2 then
        n1, n2
      else
        n2, n1
    in
    n2.n_next <- n1;
    n1.n_size <- n1.n_size + n2.n_size
  )

let same_class (self : t) (t1 : T.t) (t2 : T.t) : bool =
  let n1 = add_ self t1 |> Node.root in
  let n2 = add_ self t2 |> Node.root in
  n1 == n2
