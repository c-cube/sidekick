 
module H = CCHash

type ('f, 't, 'ts) view = ('f, 't, 'ts) Mini_cc_intf.view =
  | Bool of bool
  | App of 'f * 'ts
  | If of 't * 't * 't

type res = Mini_cc_intf.res =
  | Sat
  | Unsat

module type ARG = Mini_cc_intf.ARG
module type S = Mini_cc_intf.S

module Make(A: ARG) = struct
  module Fun = A.Fun
  module T = A.Term
  type fun_ = A.Fun.t
  type term = T.t

  module T_tbl = CCHashtbl.Make(T)

  type node = {
    n_t: term;
    mutable n_next: node; (* next in class *)
    mutable n_size: int; (* size of parent list *)
    mutable n_parents: node list;
    mutable n_root: node;
  }

  type signature = (fun_, node, node list) view

  module Node = struct
    type t = node
    let[@inline] equal (n1:t) n2 = T.equal n1.n_t n2.n_t
    let[@inline] hash (n:t) = T.hash n.n_t
    let[@inline] size (n:t) = n.n_size
    let pp out n = T.pp out n.n_t

    let add_parent (self:t) ~p : unit =
      self.n_parents <- p :: self.n_parents;
      self.n_size <- 1 + self.n_size;
      ()

    let make (t:T.t) : t =
      let rec n = {
        n_t=t; n_size=0; n_next=n;
        n_parents=[]; n_root=n;
      } in
      n

    (* iterate over the class *)
    let iter_cls (n0:t) f : unit =
      let rec aux n =
        f n;
        let n' = n.n_next in
        if equal n' n0 then () else aux n'
      in
      aux n0
  end

  module Signature = struct
    type t = signature
    let equal (s1:t) s2 : bool =
      match s1, s2 with
      | Bool b1, Bool b2 -> b1=b2
      | App (f1,[]), App (f2,[]) -> Fun.equal f1 f2
      | App (f1,l1), App (f2,l2) ->
        Fun.equal f1 f2 && CCList.equal Node.equal l1 l2
      | If (a1,b1,c1), If (a2,b2,c2) ->
        Node.equal a1 a2 && Node.equal b1 b2 && Node.equal c1 c2
      | Bool _, _ | App _, _ | If _, _
        -> false

    let hash (s:t) : int =
      match s with
      | Bool b -> H.combine2 10 (H.bool b)
      | App (f, l) -> H.combine3 20 (Fun.hash f) (H.list Node.hash l)
      | If (a,b,c) -> H.combine4 30 (Node.hash a)(Node.hash b)(Node.hash c)

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App (f, []) -> Fun.pp out f
      | App (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list Node.pp) l
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" Node.pp a Node.pp b Node.pp c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)

  type t = {
    tbl: node T_tbl.t;
    sig_tbl: node Sig_tbl.t;
    combine: (node * node) Vec.t;
    pending: node Vec.t; (* refresh signature *)
    distinct: node list ref Vec.t; (* disjoint sets *)
  }

  let create() : t =
    { tbl= T_tbl.create 128;
      sig_tbl=Sig_tbl.create 128;
      combine=Vec.create();
      pending=Vec.create();
      distinct=Vec.create();
    }

  let sub_ t k : unit =
    match T.view t with
    | Bool _ -> ()
    | App (_, args) -> args k
    | If(a,b,c) -> k a; k b; k c

  let rec add_t (self:t) (t:term) : node =
    match T_tbl.find self.tbl t with
    | n -> n
    | exception Not_found ->
      let node = Node.make t in
      (* add sub-terms, and add [t] to their parent list *)
      sub_ t
        (fun u ->
          let n_u = add_t self u in
          Node.add_parent n_u ~p:node);
      T_tbl.add self.tbl t node;
      (* need to compute signature *)
      Vec.push self.pending node;
      node

  (* find representative *)
  let[@inline] find_ (n:node) : node =
    let r = n.n_root in
    assert (Node.equal r.n_root r);
    r

  let find_t_ (self:t) (t:term): node =
    let n =
      try T_tbl.find self.tbl t
      with Not_found -> Error.errorf "minicc.find_t: no node for %a" T.pp t
    in
    find_ n

  (* does this list contain a duplicate? *)
  let has_dups (l:node list) : bool =
    Sequence.diagonal (Sequence.of_list l)
    |> Sequence.exists (fun (n1,n2) -> Node.equal n1 n2)

  exception E_unsat

  let check_distinct_ self : unit =
    Vec.iter
      (fun r ->
         r := List.map find_ !r;
         if has_dups !r then raise_notrace E_unsat)
      self.distinct

  let update_sig_ (self:t) (n: node) : unit =
    let aux s =
      Log.debugf 5 (fun k->k "(@[minicc.update-sig@ %a@])" Signature.pp s);
      match Sig_tbl.find self.sig_tbl s with
      | n2 when Node.equal n n2 -> ()
      | n2 ->
        (* collision, merge *)
        Log.debugf 5
          (fun k->k "(@[minicc.congruence-by-sig@ %a@ %a@])" Node.pp n Node.pp n2);
        Vec.push self.combine (n,n2)
      | exception Not_found ->
        Sig_tbl.add self.sig_tbl s n
    in
    match T.view n.n_t with
    | Bool _ -> ()
    | App (f, args) ->
      let args = args |> Sequence.map (find_t_ self) |> Sequence.to_list in
      aux @@ App (f, args)
    | If (a,b,c) -> aux @@ If(find_t_ self a, find_t_ self b, find_t_ self c)

  (* merge the two classes *)
  let merge_ self (n1,n2) : unit =
    let n1 = find_ n1 in
    let n2 = find_ n2 in
    if not @@ Node.equal n1 n2 then (
      (* merge into largest class *)
      let n1, n2 = if Node.size n1 > Node.size n2 then n1, n2 else n2, n1 in
      Log.debugf 5 (fun k->k "(@[minicc.merge@ :into %a@ %a@])" Node.pp n1 Node.pp n2);

      List.iter (Vec.push self.pending) n2.n_parents; (* will change signature *)

      (* merge parent lists *)
      n1.n_parents <- List.rev_append n2.n_parents n1.n_parents;
      n1.n_size <- n2.n_size + n1.n_size;

      (* update root pointer in [n2.class] *)
      Node.iter_cls n2 (fun n -> n.n_root <- n1);
    )

  (* fixpoint of the congruence closure *)
  let fixpoint (self:t) : unit =
    while not (Vec.is_empty self.pending && Vec.is_empty self.combine) do
      while not @@ Vec.is_empty self.pending do
        update_sig_ self @@ Vec.pop self.pending
      done;
      while not @@ Vec.is_empty self.combine do
        merge_ self @@ Vec.pop self.combine
      done
    done;
    check_distinct_ self

  (* API *)

  let merge (self:t) t1 t2 : unit =
    let n1 = add_t self t1 in
    let n2 = add_t self t2 in
    Vec.push self.combine (n1,n2)

  let distinct (self:t) l =
    begin match l with
      | [] | [_] -> invalid_arg "distinct: need at least 2 terms"
      | _ -> ()
    end;
    let l = List.map (add_t self) l in
    Vec.push self.distinct (ref l)

  let check (self:t) : res =
    try fixpoint self; Sat
    with E_unsat -> Unsat

end
