open Types_

type nonrec var = var
type nonrec bvar = bvar
type nonrec term = term

type view = term_view =
  | E_type of int
  | E_var of var
  | E_bound_var of bvar
  | E_const of const
  | E_app of term * term
  | E_lam of string * term * term
  | E_pi of string * term * term

type t = term

(* 5 bits in [t.id] are used to store which store it belongs to, so we have
   a chance of detecting when the user passes a term to the wrong store *)
let store_id_bits = 5

(* mask to access the store id *)
let store_id_mask = (1 lsl store_id_bits) - 1

include Term_

let[@inline] view (e : term) : view = e.view
let[@inline] db_depth e = e.flags lsr (1 + store_id_bits)
let[@inline] has_fvars e = (e.flags lsr store_id_bits) land 1 == 1
let[@inline] store_uid e : int = e.flags land store_id_mask
let[@inline] is_closed e : bool = db_depth e == 0

let[@inline] ty e : term =
  match e.ty with
  | T_ty t -> t
  | T_ty_delayed f ->
    let ty = f () in
    e.ty <- T_ty ty;
    ty

(* open an application *)
let unfold_app (e : term) : term * term list =
  let[@unroll 1] rec aux acc e =
    match e.view with
    | E_app (f, a) -> aux (a :: acc) f
    | _ -> e, acc
  in
  aux [] e

(* debug printer *)
let expr_pp_with_ ~pp_ids ~max_depth out (e : term) : unit =
  let rec loop k ~depth names out e =
    let pp' = loop' k ~depth:(depth + 1) names in
    (match e.view with
    | E_type 0 -> Fmt.string out "Type"
    | E_type i -> Fmt.fprintf out "Type(%d)" i
    | E_var v -> Fmt.string out v.v_name
    (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
    | E_bound_var v ->
      let idx = v.bv_idx in
      (match CCList.nth_opt names idx with
      | Some n when n <> "" -> Fmt.fprintf out "%s[%d]" n idx
      | _ -> Fmt.fprintf out "_[%d]" idx)
    | E_const c -> Const.pp out c
    | (E_app _ | E_lam _) when depth > max_depth ->
      Fmt.fprintf out "@<1>…/%d" e.id
    | E_app _ ->
      let f, args = unfold_app e in
      Fmt.fprintf out "%a@ %a" pp' f (Util.pp_list pp') args
    | E_lam ("", _ty, bod) ->
      Fmt.fprintf out "(@[\\_:@[%a@].@ %a@])" pp' _ty
        (loop (k + 1) ~depth:(depth + 1) ("" :: names))
        bod
    | E_lam (n, _ty, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" n pp' _ty
        (loop (k + 1) ~depth:(depth + 1) (n :: names))
        bod
    | E_pi (_, ty, bod) when is_closed bod ->
      (* actually just an arrow *)
      Fmt.fprintf out "(@[%a@ -> %a@])"
        (loop k ~depth:(depth + 1) names)
        ty
        (loop (k + 1) ~depth:(depth + 1) ("" :: names))
        bod
    | E_pi ("", _ty, bod) ->
      Fmt.fprintf out "(@[Pi _:@[%a@].@ %a@])" pp' _ty
        (loop (k + 1) ~depth:(depth + 1) ("" :: names))
        bod
    | E_pi (n, _ty, bod) ->
      Fmt.fprintf out "(@[Pi %s:@[%a@].@ %a@])" n pp' _ty
        (loop (k + 1) ~depth:(depth + 1) (n :: names))
        bod);
    if pp_ids then Fmt.fprintf out "/%d" e.id
  and loop' k ~depth names out e =
    match e.view with
    | E_type _ | E_var _ | E_bound_var _ | E_const _ ->
      loop k ~depth names out e (* atomic expr *)
    | E_app _ | E_lam _ | E_pi _ ->
      Fmt.fprintf out "(%a)" (loop k ~depth names) e
  in
  Fmt.fprintf out "@[%a@]" (loop 0 ~depth:0 []) e

let pp_debug = expr_pp_with_ ~pp_ids:false ~max_depth:max_int
let pp_debug_with_ids = expr_pp_with_ ~pp_ids:true ~max_depth:max_int
let () = pp_debug_ := pp_debug

module AsKey = struct
  type nonrec t = term

  let equal = equal
  let compare = compare
  let hash = hash
end

module Map = CCMap.Make (AsKey)
module Set = CCSet.Make (AsKey)
module Tbl = CCHashtbl.Make (AsKey)

module Hcons = Hashcons.Make (struct
  type nonrec t = term

  let equal a b =
    match a.view, b.view with
    | E_type i, E_type j -> i = j
    | E_const c1, E_const c2 -> Const.equal c1 c2
    | E_var v1, E_var v2 -> Var.equal v1 v2
    | E_bound_var v1, E_bound_var v2 -> Bvar.equal v1 v2
    | E_app (f1, a1), E_app (f2, a2) -> equal f1 f2 && equal a1 a2
    | E_lam (_, ty1, bod1), E_lam (_, ty2, bod2) ->
      equal ty1 ty2 && equal bod1 bod2
    | E_pi (_, ty1, bod1), E_pi (_, ty2, bod2) ->
      equal ty1 ty2 && equal bod1 bod2
    | ( ( E_type _ | E_const _ | E_var _ | E_bound_var _ | E_app _ | E_lam _
        | E_pi _ ),
        _ ) ->
      false

  let hash e : int =
    match e.view with
    | E_type i -> H.combine2 10 (H.int i)
    | E_const c -> H.combine2 20 (Const.hash c)
    | E_var v -> H.combine2 30 (Var.hash v)
    | E_bound_var v -> H.combine2 40 (Bvar.hash v)
    | E_app (f, a) -> H.combine3 50 (hash f) (hash a)
    | E_lam (_, ty, bod) -> H.combine3 60 (hash ty) (hash bod)
    | E_pi (_, ty, bod) -> H.combine3 70 (hash ty) (hash bod)

  let set_id t id =
    assert (t.id == -1);
    t.id <- id
end)

module Store = struct
  type t = { (* unique ID for this store *)
             s_uid: int; s_exprs: Hcons.t }

  (* TODO: use atomic? CCAtomic? *)
  let n = ref 0

  let create () : t =
    let s_uid = !n in
    incr n;
    { s_uid; s_exprs = Hcons.create ~size:256 () }

  (* check that [e] belongs in this store *)
  let[@inline] check_e_uid (self : t) (e : term) =
    assert (self.s_uid == store_uid e)
end

type store = Store.t

let iter_shallow ~f (e : term) : unit =
  match e.view with
  | E_type _ -> ()
  | _ ->
    f false (ty e);
    (match e.view with
    | E_const _ -> ()
    | E_type _ -> assert false
    | E_var v -> f false v.v_ty
    | E_bound_var v -> f false v.bv_ty
    | E_app (hd, a) ->
      f false hd;
      f false a
    | E_lam (_, tyv, bod) | E_pi (_, tyv, bod) ->
      f false tyv;
      f true bod)

let map_shallow_ ~make ~f (e : term) : term =
  match view e with
  | E_type _ | E_const _ -> e
  | E_var v ->
    let v_ty = f false v.v_ty in
    if v_ty == v.v_ty then
      e
    else
      make (E_var { v with v_ty })
  | E_bound_var v ->
    let ty' = f false v.bv_ty in
    if v.bv_ty == ty' then
      e
    else
      make (E_bound_var { v with bv_ty = ty' })
  | E_app (hd, a) ->
    let hd' = f false hd in
    let a' = f false a in
    if a == a' && hd == hd' then
      e
    else
      make (E_app (f false hd, f false a))
  | E_lam (n, tyv, bod) ->
    let tyv' = f false tyv in
    let bod' = f true bod in
    if tyv == tyv' && bod == bod' then
      e
    else
      make (E_lam (n, tyv', bod'))
  | E_pi (n, tyv, bod) ->
    let tyv' = f false tyv in
    let bod' = f true bod in
    if tyv == tyv' && bod == bod' then
      e
    else
      make (E_pi (n, tyv', bod'))

exception IsSub

let[@inline] is_type_ e =
  match e.view with
  | E_type _ -> true
  | _ -> false

let iter_dag ?(seen = Tbl.create 8) ~iter_ty ~f e : unit =
  let rec loop e =
    if not (Tbl.mem seen e) then (
      Tbl.add seen e ();
      if iter_ty && not (is_type_ e) then loop (ty e);
      f e;
      iter_shallow e ~f:(fun _ u -> loop u)
    )
  in
  loop e

exception E_exit

let exists_shallow ~f e : bool =
  try
    iter_shallow e ~f:(fun b x -> if f b x then raise_notrace E_exit);
    false
  with E_exit -> true

let for_all_shallow ~f e : bool =
  try
    iter_shallow e ~f:(fun b x -> if not (f b x) then raise_notrace E_exit);
    true
  with E_exit -> false

let contains e ~sub : bool =
  try
    iter_dag ~iter_ty:true e ~f:(fun e' ->
        if equal e' sub then raise_notrace IsSub);
    false
  with IsSub -> true

let free_vars_iter e : var Iter.t =
 fun yield ->
  iter_dag ~iter_ty:true e ~f:(fun e' ->
      match view e' with
      | E_var v -> yield v
      | _ -> ())

let free_vars ?(init = Var.Set.empty) e : Var.Set.t =
  let set = ref init in
  free_vars_iter e (fun v -> set := Var.Set.add v !set);
  !set

module Make_ = struct
  let compute_db_depth_ e : int =
    if is_type_ e then
      0
    else (
      let d1 = db_depth @@ ty e in
      let d2 =
        match view e with
        | E_type _ | E_const _ | E_var _ -> 0
        | E_bound_var v -> v.bv_idx + 1
        | E_app (a, b) -> max (db_depth a) (db_depth b)
        | E_lam (_, ty, bod) | E_pi (_, ty, bod) ->
          max (db_depth ty) (max 0 (db_depth bod - 1))
      in
      max d1 d2
    )

  let compute_has_fvars_ e : bool =
    if is_type_ e then
      false
    else
      has_fvars (ty e)
      ||
      match view e with
      | E_var _ -> true
      | E_type _ | E_bound_var _ | E_const _ -> false
      | E_app (a, b) -> has_fvars a || has_fvars b
      | E_lam (_, ty, bod) | E_pi (_, ty, bod) -> has_fvars ty || has_fvars bod

  let universe_ (e : term) : int =
    match e.view with
    | E_type i -> i
    | _ -> assert false

  let[@inline] universe_of_ty_ (e : term) : int =
    match e.view with
    | E_type i -> i + 1
    | _ -> universe_ (ty e)

  module T_int_tbl = CCHashtbl.Make (struct
    type t = term * int

    let equal (t1, k1) (t2, k2) = equal t1 t2 && k1 == k2
    let hash (t, k) = H.combine3 27 (hash t) (H.int k)
  end)

  (* shift open bound variables of [e] by [n] *)
  let db_shift_ ~make (e : term) (n : int) =
    let rec loop e k : term =
      if is_closed e then
        e
      else if is_type_ e then
        e
      else (
        match view e with
        | E_bound_var bv ->
          if bv.bv_idx >= k then
            make (E_bound_var (Bvar.make (bv.bv_idx + n) bv.bv_ty))
          else
            e
        | _ ->
          map_shallow_ e ~make ~f:(fun inbind u ->
              loop u
                (if inbind then
                  k + 1
                else
                  k))
      )
    in
    assert (n >= 0);
    if n = 0 || is_closed e then
      e
    else
      loop e 0

  (* replace DB0 in [e] with [u] *)
  let db_0_replace_ ~make e ~by:u : term =
    let cache_ = T_int_tbl.create 8 in

    (* recurse in subterm [e], under [k] intermediate binders (so any
       bound variable under k is bound by them) *)
    let rec aux e k : term =
      if is_type_ e then
        e
      else if db_depth e < k then
        e
      else (
        match view e with
        | E_const _ -> e
        | E_bound_var bv when bv.bv_idx = k ->
          (* replace [bv] with [u], and shift [u] to account for the
             [k] intermediate binders we traversed to get to [bv] *)
          db_shift_ ~make u k
        | _ ->
          (* use the cache *)
          (try T_int_tbl.find cache_ (e, k)
           with Not_found ->
             let r =
               map_shallow_ e ~make ~f:(fun inb u ->
                   aux u
                     (if inb then
                       k + 1
                     else
                       k))
             in
             T_int_tbl.add cache_ (e, k) r;
             r)
      )
    in
    if is_closed e then
      e
    else
      aux e 0

  let compute_ty_ store ~make (view : view) : term =
    match view with
    | E_var v -> Var.ty v
    | E_bound_var v -> Bvar.ty v
    | E_type i -> make (E_type (i + 1))
    | E_const c ->
      let ty = Const.ty c in
      Store.check_e_uid store ty;
      if not (is_closed ty) then
        Error.errorf "const %a@ cannot have a non-closed type like %a" Const.pp
          c pp_debug ty;
      ty
    | E_lam (name, ty_v, bod) ->
      Store.check_e_uid store ty_v;
      Store.check_e_uid store bod;
      (* type of [\x:tau. bod] is [pi x:tau. typeof(bod)] *)
      let ty_bod = ty bod in
      make (E_pi (name, ty_v, ty_bod))
    | E_app (f, a) ->
      (* type of [f a], where [a:tau] and [f: Pi x:tau. ty_bod_f],
         is [ty_bod_f[x := a]] *)
      Store.check_e_uid store f;
      Store.check_e_uid store a;
      let ty_f = ty f in
      let ty_a = ty a in
      (match ty_f.view with
      | E_pi (_, ty_arg_f, ty_bod_f) ->
        (* check that the expected type matches *)
        if not (equal ty_arg_f ty_a) then
          Error.errorf
            "@[<2>cannot @[apply `%a`@]@ @[to `%a`@],@ expected argument type: \
             `%a`@ @[actual: `%a`@]@]"
            pp_debug f pp_debug a pp_debug_with_ids ty_arg_f pp_debug_with_ids
            ty_a;
        db_0_replace_ ~make ty_bod_f ~by:a
      | _ ->
        Error.errorf
          "@[<2>cannot apply %a,@ must have Pi type, but actual type is %a@]"
          pp_debug f pp_debug ty_f)
    | E_pi (_, ty, bod) ->
      (* TODO: check the actual triplets for COC *)
      (*Fmt.printf "pi %a %a@." pp_debug ty pp_debug bod;*)
      Store.check_e_uid store ty;
      Store.check_e_uid store bod;
      let u = max (universe_of_ty_ ty) (universe_of_ty_ bod) in
      make (E_type u)

  let ty_assert_false_ () = assert false

  (* hashconsing + computing metadata + computing type (for new terms) *)
  let rec make_ (store : store) view : term =
    let e = { view; ty = T_ty_delayed ty_assert_false_; id = -1; flags = 0 } in
    let e2 = Hcons.hashcons store.s_exprs e in
    if e == e2 then (
      (* new term, compute metadata *)
      assert (store.s_uid land store_id_mask == store.s_uid);

      (* first, compute type *)
      (match e.view with
      | E_type i ->
        (* cannot force type now, as it's an infinite tower of types.
           Instead we will produce the type on demand. *)
        let get_ty () = make_ store (E_type (i + 1)) in
        e.ty <- T_ty_delayed get_ty
      | _ ->
        let ty = compute_ty_ store ~make:(make_ store) view in
        e.ty <- T_ty ty);
      let has_fvars = compute_has_fvars_ e in
      e2.flags <-
        (compute_db_depth_ e lsl (1 + store_id_bits))
        lor (if has_fvars then
              1 lsl store_id_bits
            else
              0)
        lor store.s_uid;
      Store.check_e_uid store e2
    );
    e2

  let type_of_univ store i : term = make_ store (E_type i)
  let type_ store : term = type_of_univ store 0
  let var store v : term = make_ store (E_var v)
  let var_str store name ~ty : term = var store (Var.make name ty)
  let bvar store v : term = make_ store (E_bound_var v)
  let bvar_i store i ~ty : term = make_ store (E_bound_var (Bvar.make i ty))
  let const store c : term = make_ store (E_const c)
  let app store f a = make_ store (E_app (f, a))
  let app_l store f l = List.fold_left (app store) f l

  (* general substitution, compatible with DB indices. We use this
     also to abstract on a free variable, because it subsumes it and
     it's better to minimize the number of DB indices manipulations *)
  let subst_ ~make ~recursive e0 (subst : subst) : t =
    (* cache for types and some terms *)
    let cache_ = T_int_tbl.create 16 in

    let rec loop k e =
      if is_type_ e then
        e
      else if not (has_fvars e) then
        (* no free variables, cannot change *)
        e
      else (
        try T_int_tbl.find cache_ (e, k)
        with Not_found ->
          let r = loop_uncached_ k e in
          T_int_tbl.add cache_ (e, k) r;
          r
      )
    and loop_uncached_ k (e : t) : t =
      match view e with
      | E_var v ->
        (* first, subst in type *)
        let v = { v with v_ty = loop k v.v_ty } in
        (match Var_.Map.find v subst.m with
        | u ->
          let u = db_shift_ ~make u k in
          if recursive then
            loop 0 u
          else
            u
        | exception Not_found -> make (E_var v))
      | E_const _ -> e
      | _ ->
        map_shallow_ e ~make ~f:(fun inb u ->
            loop
              (if inb then
                k + 1
              else
                k)
              u)
    in

    if Var_.Map.is_empty subst.m then
      e0
    else
      loop 0 e0

  module DB = struct
    let subst_db0 store e ~by : t = db_0_replace_ ~make:(make_ store) e ~by

    let shift store t ~by : t =
      assert (by >= 0);
      db_shift_ ~make:(make_ store) t by

    let lam_db ?(var_name = "") store ~var_ty bod : term =
      make_ store (E_lam (var_name, var_ty, bod))

    let pi_db ?(var_name = "") store ~var_ty bod : term =
      make_ store (E_pi (var_name, var_ty, bod))

    let abs_on (store : store) (v : var) (e : term) : term =
      Store.check_e_uid store v.v_ty;
      Store.check_e_uid store e;
      if not (is_closed v.v_ty) then
        Error.errorf "cannot abstract on variable@ with non closed type %a"
          pp_debug v.v_ty;
      let db0 = bvar store (Bvar.make 0 v.v_ty) in
      let body = db_shift_ ~make:(make_ store) e 1 in
      subst_ ~make:(make_ store) ~recursive:false body
        { m = Var_.Map.singleton v db0 }
  end

  let lam store v bod : term =
    let bod' = DB.abs_on store v bod in
    DB.lam_db ~var_name:(Var.name v) store ~var_ty:(Var.ty v) bod'

  let pi store v bod : term =
    let bod' = DB.abs_on store v bod in
    DB.pi_db ~var_name:(Var.name v) store ~var_ty:(Var.ty v) bod'

  let arrow store a b : term =
    let b' = DB.shift store b ~by:1 in
    DB.pi_db store ~var_ty:a b'

  let arrow_l store args ret = List.fold_right (arrow store) args ret

  (* find a name that doesn't capture a variable of [e] *)
  let pick_name_ (name0 : string) (e : term) : string =
    let rec loop i =
      let name =
        if i = 0 then
          name0
        else
          Printf.sprintf "%s%d" name0 i
      in
      if free_vars_iter e |> Iter.exists (fun v -> v.v_name = name) then
        loop (i + 1)
      else
        name
    in
    loop 0

  let open_lambda store e : _ option =
    match view e with
    | E_lam (name, ty, bod) ->
      let name = pick_name_ name bod in
      let v = Var.make name ty in
      let bod' = DB.subst_db0 store bod ~by:(var store v) in
      Some (v, bod')
    | _ -> None

  let open_lambda_exn store e =
    match open_lambda store e with
    | Some tup -> tup
    | None -> Error.errorf "open-lambda: term is not a lambda:@ %a" pp_debug e
end

include Make_

let map_shallow store ~f e : t = map_shallow_ ~make:(make_ store) ~f e

(* re-export some internal things *)
module Internal_ = struct
  let is_type_ = is_type_

  let subst_ store ~recursive t subst =
    subst_ ~make:(make_ store) ~recursive t subst
end
