open Types_

type bvar = Bvar.t
type nonrec term = term
type nonrec binder = binder = BD | BI | BS | BC

type view = term_view =
  | E_type of level
  | E_bound_var of bvar
  | E_const of const * level list
  | E_app of term * term
  | E_lam of binder * string * term * term
  | E_pi of binder * string * term * term

type t = term

(* mask to access the store id *)
let[@inline] view (e : term) : view = e.view
let[@inline] db_depth e = e.flags
let[@inline] is_closed e : bool = db_depth e == 0

(* open an application *)
let[@inline] unfold_app (e : term) : term * term list =
  let[@unroll 1] rec aux acc e =
    match e.view with
    | E_app (f, a) -> aux (a :: acc) f
    | _ -> e, acc
  in
  aux [] e

let[@inline] is_const e =
  match e.view with
  | E_const _ -> true
  | _ -> false

let[@inline] is_app e =
  match e.view with
  | E_app _ -> true
  | _ -> false

let[@inline] is_pi e =
  match e.view with
  | E_pi _ -> true
  | _ -> false

let as_type e : level option =
  match e.view with
  | E_type l -> Some l
  | _ -> None

let string_of_binder = function
  | BI -> "BI"
  | BS -> "BS"
  | BC -> "BC"
  | BD -> "BD"

(* debug printer *)
let expr_pp_with_ ~max_depth out (e : term) : unit =
  let rec loop k ~depth names out e =
    let pp' = loop k ~depth:(depth + 1) names in
    match e.view with
    | E_type lvl when Level.is_one lvl -> Fmt.string out "Type"
    | E_type lvl -> Fmt.fprintf out "Type.{%a}" Level.pp lvl
    | E_bound_var v ->
      let idx = v.bv_idx in
      (match CCList.nth_opt names idx with
      | Some n when n <> "" -> Fmt.fprintf out "%s[%d]" n idx
      | _ -> Fmt.fprintf out "_[%d]" idx)
    | E_const (c, []) -> Const.pp out c
    | E_const (c, args) ->
      Fmt.fprintf out "(@[%a@ %a@])" Const.pp c (Util.pp_list Level.pp) args
    | (E_app _ | E_lam _) when depth > max_depth -> Fmt.fprintf out "@<1>…"
    | E_app _ ->
      let f, args = unfold_app e in
      Fmt.fprintf out "(%a@ %a)" pp' f (Util.pp_list pp') args
    | E_lam (binder, name, _ty, bod) ->
      Fmt.fprintf out "(@[\\[%s]%s:@[%a@].@ %a@])" (string_of_binder binder)
        name pp' _ty
        (loop (k + 1) ~depth:(depth + 1) ("" :: names))
        bod
    | E_pi (binder, name, ty_arg, bod) ->
      Fmt.fprintf out "(@[Pi[%s] %s:@[%a@].@ %a@])" (string_of_binder binder)
        name pp' ty_arg
        (loop (k + 1) ~depth:(depth + 1) ("" :: names))
        bod
  in
  Fmt.fprintf out "@[%a@]" (loop 0 ~depth:0 []) e

let pp_debug = expr_pp_with_ ~max_depth:max_int

let as_type_exn e : level =
  match e.view with
  | E_type l -> l
  | _ -> Error.errorf "Term.as_type_exn: `%a` is not a type" pp_debug e

let iter_shallow ~f (e : term) : unit =
  match e.view with
  | E_type _ -> ()
  | _ ->
    (match e.view with
    | E_const _ -> ()
    | E_type _ -> assert false
    | E_bound_var _ -> ()
    | E_app (hd, a) ->
      f false hd;
      f false a
    | E_lam (_, _, tyv, bod) | E_pi (_, _, tyv, bod) ->
      f false tyv;
      f true bod)

let[@inline] is_type e =
  match e.view with
  | E_type _ -> true
  | _ -> false

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

let compute_db_depth_ e : int =
  if is_type e then
    0
  else (
    let d =
      match view e with
      | E_type _ | E_const _ -> 0
      | E_bound_var v -> v.bv_idx + 1
      | E_app (a, b) -> max (db_depth a) (db_depth b)
      | E_lam (_, _, ty, bod) | E_pi (_, _, ty, bod) ->
        max (db_depth ty) (max 0 (db_depth bod - 1))
    in
    d
  )

let make_ view : term =
  let e = { view; flags = 0 } in
  let flags = compute_db_depth_ e in
  e.flags <- flags;
  e

let map_shallow ~f (e : term) : term =
  match view e with
  | E_type _ | E_const _ | E_bound_var _ -> e
  | E_app (hd, a) ->
    let hd' = f false hd in
    let a' = f false a in
    if a == a' && hd == hd' then
      e
    else
      make_ (E_app (f false hd, f false a))
  | E_lam (b, name, tyv, bod) ->
    let tyv' = f false tyv in
    let bod' = f true bod in
    if tyv == tyv' && bod == bod' then
      e
    else
      make_ (E_lam (b, name, tyv', bod'))
  | E_pi (b, name, tyv, bod) ->
    let tyv' = f false tyv in
    let bod' = f true bod in
    if tyv == tyv' && bod == bod' then
      e
    else
      make_ (E_pi (b, name, tyv', bod'))

(* shift open bound variables of [e] by [n] *)
let db_shift_ (e : term) (n : int) =
  let rec loop e k : term =
    if is_closed e || db_depth e < k then
      e
    else if is_type e then
      e
    else (
      match view e with
      | E_bound_var bv ->
        if bv.bv_idx >= k then
          make_ (E_bound_var (Bvar.make (bv.bv_idx + n)))
        else
          e
      | _ ->
        map_shallow e ~f:(fun inbind u ->
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
let db_replace_ e (env : t list) : term =
  let len_env = List.length env in

  (* recurse in subterm [e], under [k] intermediate binders (so any
     bound variable under k is bound by them) *)
  let rec aux e k : term =
    if is_type e then
      e
    else if db_depth e < k then
      (* no open variable *)
      e
    else (
      match view e with
      | E_const _ -> e
      | E_bound_var v when v.bv_idx >= k && v.bv_idx < k + len_env ->
        (* replace [v] with [env[v-k]], and shift it to account for the
           [k] intermediate binders we traversed to get to [v] *)
        let u = List.nth env (v.bv_idx - k) in
        db_shift_ u k
      | _ ->
        map_shallow e ~f:(fun inb u ->
            aux u
              (if inb then
                k + 1
              else
                k))
    )
  in
  if is_closed e then
    e
  else if len_env = 0 then
    e
  else
    aux e 0

let[@inline] type_of_univ lvl : term = make_ (E_type lvl)
let[@inline] type_of_univ_int i : term = type_of_univ (Level.of_int i)
let type_ : term = type_of_univ Level.one
let[@inline] bvar v : term = make_ (E_bound_var v)
let[@inline] bvar_i i : term = make_ (E_bound_var (Bvar.make i))
let[@inline] const c args : term = make_ (E_const (c, args))
let[@inline] app f a : term = make_ (E_app (f, a))
let[@inline] app_l f l : term = List.fold_left app f l
let[@inline] lam b str ~var_ty bod : term = make_ (E_lam (b, str, var_ty, bod))
let[@inline] pi b str ~var_ty bod : term = make_ (E_pi (b, str, var_ty, bod))

module DB = struct
  let[@inline] subst_db0 e ~by : t = db_replace_ e [ by ]
  let[@inline] subst_db_l e env : t = db_replace_ e env

  let[@inline] shift t ~by : t =
    assert (by >= 0);
    db_shift_ t by
end
