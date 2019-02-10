
type res =
  | Sat
  | Unsat

module type TERM = CC_types.TERM

module type S = sig
  type term
  type fun_
  type term_state

  type t

  val create : term_state -> t

  val add_lit : t -> term -> bool -> unit
  val distinct : t -> term list -> unit

  val check : t -> res
end


module Make(A: TERM) = struct
  open CC_types

  module Fun = A.Fun
  module T = A.Term
  type fun_ = A.Fun.t
  type term = T.t
  type term_state = A.Term.state

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
      | App_fun (f1,[]), App_fun (f2,[]) -> Fun.equal f1 f2
      | App_fun (f1,l1), App_fun (f2,l2) ->
        Fun.equal f1 f2 && CCList.equal Node.equal l1 l2
      | App_ho (f1,l1), App_ho (f2,l2) ->
        Node.equal f1 f2 && CCList.equal Node.equal l1 l2
      | If (a1,b1,c1), If (a2,b2,c2) ->
        Node.equal a1 a2 && Node.equal b1 b2 && Node.equal c1 c2
      | Eq (a1,b1), Eq (a2,b2) ->
        Node.equal a1 a2 && Node.equal b1 b2
      | Opaque u1, Opaque u2 -> Node.equal u1 u2
      | Bool _, _ | App_fun _, _ | App_ho _, _ | If _, _
      | Eq _, _ | Opaque _, _
        -> false

    let hash (s:t) : int =
      let module H = CCHash in
      match s with
      | Bool b -> H.combine2 10 (H.bool b)
      | App_fun (f, l) -> H.combine3 20 (Fun.hash f) (H.list Node.hash l)
      | App_ho (f, l) -> H.combine3 30 (Node.hash f) (H.list Node.hash l)
      | Eq (a,b) -> H.combine3 40 (Node.hash a) (Node.hash b)
      | Opaque u -> H.combine2 50 (Node.hash u)
      | If (a,b,c) -> H.combine4 60 (Node.hash a)(Node.hash b)(Node.hash c)

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list Node.pp) l
      | App_ho (f, []) -> Node.pp out f
      | App_ho (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Node.pp f (Util.pp_list Node.pp) l
      | Opaque t -> Node.pp out t
      | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" Node.pp a Node.pp b
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" Node.pp a Node.pp b Node.pp c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)

  type t = {
    mutable ok: bool; (* unsat? *)
    tbl: node T_tbl.t;
    sig_tbl: node Sig_tbl.t;
    combine: (node * node) Vec.t;
    pending: node Vec.t; (* refresh signature *)
    distinct: node list ref Vec.t; (* disjoint sets *)
    true_: node;
    false_: node;
  }

  let create tst : t =
    let true_ = T.bool tst true in
    let false_ = T.bool tst false in
    let self = {
      ok=true;
      tbl= T_tbl.create 128;
      sig_tbl=Sig_tbl.create 128;
      combine=Vec.create();
      pending=Vec.create();
      distinct=Vec.create();
      true_=Node.make true_;
      false_=Node.make false_;
    } in
    T_tbl.add self.tbl true_ self.true_;
    T_tbl.add self.tbl false_ self.false_;
    self

  let sub_ t k : unit =
    match T.cc_view t with
    | Bool _ | Opaque _ -> ()
    | App_fun (_, args) -> args k
    | App_ho (f, args) -> k f; args k
    | Eq (a,b) -> k a; k b
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

  let compute_sig (self:t) (n:node) : Signature.t option =
    let[@inline] return x = Some x in
    match T.cc_view n.n_t with
    | Bool _ | Opaque _ -> None
    | Eq (a,b) ->
      let a = find_t_ self a in
      let b = find_t_ self b in
      return @@ Eq (a,b)
    | App_fun (f, args) ->
      let args = args |> Sequence.map (find_t_ self) |> Sequence.to_list in
      if args<>[] then (
        return @@ App_fun (f, args)
      ) else None
    | App_ho (f, args) ->
      let args = args |> Sequence.map (find_t_ self) |> Sequence.to_list in
      return @@ App_ho (find_t_ self f, args)
    | If (a,b,c) ->
      return @@ If(find_t_ self a, find_t_ self b, find_t_ self c)

  let update_sig_ (self:t) (n: node) : unit =
    match compute_sig self n with
    | None -> ()
    | Some (Eq (a,b)) ->
      if Node.equal a b then (
        (* reduce to [true] *)
        let n2 = self.true_ in
        Log.debugf 5
          (fun k->k "(@[minicc.congruence-by-eq@ %a@ %a@])" Node.pp n Node.pp n2);
        Vec.push self.combine (n,n2)
      )
    | Some s ->
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

  let[@inline] is_bool self n = Node.equal self.true_ n || Node.equal self.false_ n

  (* merge the two classes *)
  let merge_ self (n1,n2) : unit =
    let n1 = find_ n1 in
    let n2 = find_ n2 in
    if not @@ Node.equal n1 n2 then (
      (* merge into largest class, or into a boolean *)
      let n1, n2 =
        if is_bool self n1 then n1, n2
        else if is_bool self n2 then n2, n1
        else if Node.size n1 > Node.size n2 then n1, n2
        else n2, n1 in
      Log.debugf 5 (fun k->k "(@[minicc.merge@ :into %a@ %a@])" Node.pp n1 Node.pp n2);

      if is_bool self n1 && is_bool self n2 then (
        Log.debugf 5 (fun k->k "(minicc.conflict.merge-true-false)");
        self.ok <- false;
        raise E_unsat
      );

      List.iter (Vec.push self.pending) n2.n_parents; (* will change signature *)

      (* merge parent lists *)
      n1.n_parents <- List.rev_append n2.n_parents n1.n_parents;
      n1.n_size <- n2.n_size + n1.n_size;

      (* update root pointer in [n2.class] *)
      Node.iter_cls n2 (fun n -> n.n_root <- n1);
    )

  let check_ok_ self =
    if not self.ok then raise_notrace E_unsat

  (* fixpoint of the congruence closure *)
  let fixpoint (self:t) : unit =
    while not (Vec.is_empty self.pending && Vec.is_empty self.combine) do
      check_ok_ self;
      while not @@ Vec.is_empty self.pending do
        update_sig_ self @@ Vec.pop self.pending
      done;
      while not @@ Vec.is_empty self.combine do
        merge_ self @@ Vec.pop self.combine
      done
    done;
    check_distinct_ self

  (* API *)

  let add_lit (self:t) (p:T.t) (sign:bool) : unit =
    match T.cc_view p with
    | Eq (t1,t2) when sign ->
      let n1 = add_t self t1 in
      let n2 = add_t self t2 in
      Vec.push self.combine (n1,n2)
    | _ ->
      (* just merge with true/false *)
      let n = add_t self p in
      let n2 =  if sign then self.true_ else self.false_ in
      Vec.push self.combine (n,n2)

  let distinct (self:t) l =
    begin match l with
      | [] | [_] -> invalid_arg "distinct: need at least 2 terms"
      | _ -> ()
    end;
    let l = List.map (add_t self) l in
    Vec.push self.distinct (ref l)

  let check (self:t) : res =
    try fixpoint self; Sat
    with E_unsat ->
      self.ok <- false;
      Unsat

end
