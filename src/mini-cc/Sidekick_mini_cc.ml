module CC_view = Sidekick_core.CC_view

module type ARG = sig
  module T : Sidekick_core.TERM

  val cc_view : T.Term.t -> (T.Fun.t, T.Term.t, T.Term.t Iter.t) CC_view.t
end

module type S = sig
  type term
  type fun_
  type term_state

  type t

  val create : term_state -> t

  val clear : t -> unit

  val add_lit : t -> term -> bool -> unit

  val check_sat : t -> bool

  val classes : t -> term Iter.t Iter.t
end

module Make(A: ARG) = struct
  open CC_view

  module Fun = A.T.Fun
  module T = A.T.Term
  type fun_ = A.T.Fun.t
  type term = T.t
  type term_state = T.state

  module T_tbl = CCHashtbl.Make(T)

  type node = {
    n_t: term;
    mutable n_next: node; (* next in class *)
    mutable n_size: int; (* size of class *)
    mutable n_parents: node list;
    mutable n_root: node; (* root of the class *)
  }

  type signature = (fun_, node, node list) CC_view.t

  module Node = struct
    type t = node
    let[@inline] equal (n1:t) n2 = T.equal n1.n_t n2.n_t
    let[@inline] hash (n:t) = T.hash n.n_t
    let[@inline] size (n:t) = n.n_size
    let[@inline] is_root n = n == n.n_root
    let[@inline] root n = n.n_root
    let[@inline] term n = n.n_t
    let pp out n = T.pp out n.n_t

    let add_parent (self:t) ~p : unit =
      self.n_parents <- p :: self.n_parents

    let make (t:T.t) : t =
      let rec n = {
        n_t=t; n_size=1; n_next=n;
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
      | Not n1, Not n2 -> Node.equal n1 n2
      | If (a1,b1,c1), If (a2,b2,c2) ->
        Node.equal a1 a2 && Node.equal b1 b2 && Node.equal c1 c2
      | Eq (a1,b1), Eq (a2,b2) ->
        Node.equal a1 a2 && Node.equal b1 b2
      | Opaque u1, Opaque u2 -> Node.equal u1 u2
      | Bool _, _ | App_fun _, _ | App_ho _, _ | If _, _
      | Eq _, _ | Opaque _, _ | Not _, _
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
      | Not u -> H.combine2 70 (Node.hash u)

    let pp out = function
      | Bool b -> Fmt.bool out b
      | App_fun (f, []) -> Fun.pp out f
      | App_fun (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Fun.pp f (Util.pp_list Node.pp) l
      | App_ho (f, []) -> Node.pp out f
      | App_ho (f, l) -> Fmt.fprintf out "(@[%a@ %a@])" Node.pp f (Util.pp_list Node.pp) l
      | Opaque t -> Node.pp out t
      | Not u -> Fmt.fprintf out "(@[not@ %a@])" Node.pp u
      | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" Node.pp a Node.pp b
      | If (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" Node.pp a Node.pp b Node.pp c
  end

  module Sig_tbl = CCHashtbl.Make(Signature)

  type t = {
    mutable ok: bool; (* unsat? *)
    tbl: node T_tbl.t;
    sig_tbl: node Sig_tbl.t;
    mutable combine: (node * node) list;
    mutable pending: node list; (* refresh signature *)
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
      combine=[];
      pending=[];
      true_=Node.make true_;
      false_=Node.make false_;
    } in
    T_tbl.add self.tbl true_ self.true_;
    T_tbl.add self.tbl false_ self.false_;
    self

  let clear (self:t) : unit =
    let {ok=_; tbl; sig_tbl; pending=_; combine=_; true_; false_} = self in
    self.ok <- true;
    self.pending <- [];
    self.combine <- [];
    T_tbl.clear tbl;
    Sig_tbl.clear sig_tbl;
    T_tbl.add tbl true_.n_t true_;
    T_tbl.add tbl false_.n_t false_;
    ()

  let sub_ t k : unit =
    match A.cc_view t with
    | Bool _ | Opaque _ -> ()
    | App_fun (_, args) -> args k
    | App_ho (f, args) -> k f; args k
    | Eq (a,b) -> k a; k b
    | Not u -> k u
    | If(a,b,c) -> k a; k b; k c

  let rec add_t (self:t) (t:term) : node =
    match T_tbl.find self.tbl t with
    | n -> n
    | exception Not_found ->
      let node = Node.make t in
      T_tbl.add self.tbl t node;
      (* add sub-terms, and add [t] to their parent list *)
      sub_ t
        (fun u ->
          let n_u = Node.root @@ add_t self u in
          Node.add_parent n_u ~p:node);
      (* need to compute signature *)
      self.pending <- node :: self.pending;
      node

  let find_t_ (self:t) (t:term): node =
    try T_tbl.find self.tbl t |> Node.root
    with Not_found -> Error.errorf "mini-cc.find_t: no node for %a" T.pp t

  exception E_unsat

  let compute_sig (self:t) (n:node) : Signature.t option =
    let[@inline] return x = Some x in
    match A.cc_view n.n_t with
    | Bool _ | Opaque _ -> None
    | Eq (a,b) ->
      let a = find_t_ self a in
      let b = find_t_ self b in
      return @@ Eq (a,b)
    | Not u -> return @@ Not (find_t_ self u)
    | App_fun (f, args) ->
      let args = args |> Iter.map (find_t_ self) |> Iter.to_list in
      if args<>[] then (
        return @@ App_fun (f, args)
      ) else None
    | App_ho (f, args) ->
      let args = args |> Iter.map (find_t_ self) |> Iter.to_list in
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
          (fun k->k "(@[mini-cc.congruence-by-eq@ %a@ %a@])" Node.pp n Node.pp n2);
        self.combine <- (n,n2) :: self.combine;
      )
    | Some (Not u) when Node.equal u self.true_ ->
      self.combine <- (n,self.false_) :: self.combine
    | Some (Not u) when Node.equal u self.false_ ->
      self.combine <- (n,self.true_) :: self.combine
    | Some (If (a,b,_)) when Node.equal a self.true_ ->
      self.combine <- (n,b) :: self.combine
    | Some (If (a,_,c)) when Node.equal a self.false_ ->
      self.combine <- (n,c) :: self.combine
    | Some s ->
      Log.debugf 5 (fun k->k "(@[mini-cc.update-sig@ %a@])" Signature.pp s);
      match Sig_tbl.find self.sig_tbl s with
      | n2 when Node.equal n n2 -> ()
      | n2 ->
        (* collision, merge *)
        Log.debugf 5
          (fun k->k "(@[mini-cc.congruence-by-sig@ %a@ %a@])" Node.pp n Node.pp n2);
        self.combine <- (n,n2) :: self.combine;
      | exception Not_found ->
        Sig_tbl.add self.sig_tbl s n

  let[@inline] is_bool self n = Node.equal self.true_ n || Node.equal self.false_ n

  (* merge the two classes *)
  let merge_ self n1 n2 : unit =
    let n1 = Node.root n1 in
    let n2 = Node.root n2 in
    if not @@ Node.equal n1 n2 then (
      (* merge into largest class, or into a boolean *)
      let n1, n2 =
        if is_bool self n1 then n1, n2
        else if is_bool self n2 then n2, n1
        else if Node.size n1 > Node.size n2 then n1, n2
        else n2, n1 in
      Log.debugf 5 (fun k->k "(@[mini-cc.merge@ :into %a@ %a@])" Node.pp n1 Node.pp n2);

      if is_bool self n1 && is_bool self n2 then (
        Log.debugf 5 (fun k->k "(mini-cc.conflict.merge-true-false)");
        self.ok <- false;
        raise E_unsat
      );

      self.pending <- List.rev_append n2.n_parents self.pending; (* will change signature *)

      (* merge parent lists *)
      n1.n_parents <- List.rev_append n2.n_parents n1.n_parents;
      n1.n_size <- n2.n_size + n1.n_size;

      (* update root pointer in [n2.class] *)
      Node.iter_cls n2 (fun n -> n.n_root <- n1);

      (* merge classes [next] pointers *)
      let n1_next = n1.n_next in
      n1.n_next <- n2.n_next;
      n2.n_next <- n1_next;
    )

  let[@inline] check_ok_ self =
    if not self.ok then raise_notrace E_unsat

  (* fixpoint of the congruence closure *)
  let fixpoint (self:t) : unit =
    while not (CCList.is_empty self.pending && CCList.is_empty self.combine) do
      check_ok_ self;
      while not @@ CCList.is_empty self.pending do
        let n = List.hd self.pending in
        self.pending <- List.tl self.pending;
        update_sig_ self n
      done;
      while not @@ CCList.is_empty self.combine do
        let (n1,n2) = List.hd self.combine in
        self.combine <- List.tl self.combine;
        merge_ self n1 n2
      done
    done

  (* API *)

  let add_lit (self:t) (p:T.t) (sign:bool) : unit =
    match A.cc_view p with
    | Eq (t1,t2) when sign ->
      let n1 = add_t self t1 in
      let n2 = add_t self t2 in
      self.combine <- (n1,n2) :: self.combine
    | _ ->
      (* just merge with true/false *)
      let n = add_t self p in
      let n2 =  if sign then self.true_ else self.false_ in
      self.combine <- (n,n2) :: self.combine

  let check_sat (self:t) : bool =
    try fixpoint self; true
    with E_unsat ->
      self.ok <- false;
      false

  let classes self : _ Iter.t =
    T_tbl.values self.tbl
    |> Iter.filter Node.is_root
    |> Iter.map
      (fun n -> Node.iter_cls n |> Iter.map Node.term)
end
