module V = TVar

type node = { var: V.t; mutable next: node; mutable prev: node }
type t = { vars: node V.Tbl.t; mutable first: node option }

let create () : t = { vars = V.Tbl.create 32; first = None }
let[@inline] size (self : t) : int = V.Tbl.length self.vars
let[@inline] mem (self : t) (v : V.t) : bool = V.Tbl.mem self.vars v

let add (self : t) (v : V.t) : unit =
  if not (V.Tbl.mem self.vars v) then (
    let rec node = { var = v; prev = node; next = node } in
    V.Tbl.add self.vars v node;
    match self.first with
    | None -> self.first <- Some node
    | Some n_first ->
      (* insert at the end *)
      n_first.prev.next <- node;
      n_first.prev <- node;
      node.prev <- n_first.prev;
      node.next <- n_first
  )

let pop_next (self : t) : _ option =
  match self.first with
  | None -> None
  | Some n ->
    let next = n.next in
    (* remove [n] from the list *)
    next.prev <- n.prev;
    n.prev.next <- next;

    (* point to the next *)
    if next != n then
      self.first <- Some next
    else
      self.first <- None;

    Some n.var

let bump (self : t) (v : V.t) : unit =
  match V.Tbl.find_opt self.vars v with
  | None -> ()
  | Some node ->
    (* move node to front *)
    node.next.prev <- node.prev;
    node.prev.next <- node.next;

    let first =
      match self.first with
      | Some n -> n
      | None -> assert false
    in

    node.prev <- first.prev;
    node.next <- first;
    first.prev <- node;
    first.next.prev <- node;
    self.first <- Some node

let remove (self : t) (v : V.t) : unit =
  match V.Tbl.find_opt self.vars v with
  | None -> ()
  | Some node ->
    (* remove from list *)
    node.prev.next <- node.next;
    node.next.prev <- node.prev;

    (match self.first with
    | Some n when n == node -> self.first <- Some node.next
    | _ -> ());

    (* remove from table *)
    V.Tbl.remove self.vars v
