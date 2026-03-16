(** Translate sidekick Term.t to .twp E-index expressions.

    This module walks Term.t recursively and emits E-lines into the
    twp_state buffer. Results are memoized by term id.

    With -open Sidekick_core:
      Term  (includes T_builtins: C_bool, C_eq, C_not, C_true, C_false, C_ite, C_proof)
      Const  (Const.view : Const.t -> const_view)
      Str_const  (Str_const.Str : string -> const_view)
      Lit
*)

open Twp_state

(* fixed preamble indices from twp_state.ml *)
let e_type_idx = Twp_state.e_type   (* 1 *)
let e_bool_idx = Twp_state.e_bool   (* 2 *)
let e_false_idx = Twp_state.e_false (* 3 *)

(** Escape a name for use as a .twp atom. *)
let escape_name (s : string) : string =
  let ok c =
    match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '.' | '_' | '-' | '=' -> true
    | _ -> false
  in
  if String.length s > 0 && String.for_all ok s then
    s
  else (
    let buf = Buffer.create (String.length s + 2) in
    Buffer.add_char buf '"';
    String.iter
      (fun c ->
        if c = '"' then Buffer.add_string buf "\\\""
        else if c = '\\' then Buffer.add_string buf "\\\\"
        else Buffer.add_char buf c)
      s;
    Buffer.add_char buf '"';
    Buffer.contents buf
  )

(** Main entry point: emit the E-lines for [t] and return its E-index.
    Idempotent: memoized by Term.t identity. *)
let rec emit_expr (st : Twp_state.t) (t : Term.t) : int =
  match Term.Tbl.find_opt st.term_tbl t with
  | Some n -> n
  | None ->
    let n = emit_expr_uncached st t in
    Term.Tbl.replace st.term_tbl t n;
    n

and emit_expr_uncached (st : Twp_state.t) (t : Term.t) : int =
  match Term.view t with
  | Term.E_type _ ->
    e_type_idx

  | Term.E_const c ->
    emit_const st t c

  | Term.E_app (f, a) ->
    let f_idx = emit_expr st f in
    let a_idx = emit_expr st a in
    let n = alloc_e st in
    emit_line st (Printf.sprintf "E%d app E%d E%d" n f_idx a_idx);
    n

  | Term.E_pi (_, dom, body) ->
    (* Arrow type — for QF_UF, Pi is a non-dependent arrow. *)
    let dom_idx = emit_expr st dom in
    let range_idx = emit_expr st body in
    let n = alloc_e st in
    emit_line st (Printf.sprintf "E%d arrow E%d E%d" n dom_idx range_idx);
    n

  | Term.E_lam _ | Term.E_var _ | Term.E_bound_var _ | Term.E_app_fold _ ->
    let n = alloc_e st in
    emit_line st (Printf.sprintf "# unsupported term view at E%d" n);
    emit_line st (Printf.sprintf "E%d type" n);
    n

and emit_const (st : Twp_state.t) (t : Term.t) (c : Const.t) : int =
  (* T_builtins constructors are included in Term module *)
  match Const.view c with
  | Term.C_bool -> e_bool_idx
  | Term.C_false -> e_false_idx
  | Term.C_true ->
    let n = alloc_e st in
    emit_line st "const true [] E2";
    emit_line st (Printf.sprintf "E%d const true" n);
    n
  | Term.C_eq ->
    (* Bare = constant — will be applied to type arg via E_app *)
    let n = alloc_e st in
    emit_line st (Printf.sprintf "E%d const =" n);
    n
  | Term.C_not ->
    (* not : bool -> bool *)
    let n = alloc_e st in
    emit_line st (Printf.sprintf "# C_not (bool->bool) E%d" n);
    emit_line st (Printf.sprintf "E%d const bool" n);
    n
  | Term.C_ite | Term.C_proof ->
    let n = alloc_e st in
    emit_line st (Printf.sprintf "# unsupported builtin E%d" n);
    emit_line st (Printf.sprintf "E%d type" n);
    n
  | Str_const.Str name ->
    emit_str_const st t name
  | _ ->
    (* For other const_view variants (e.g. uninterpreted sorts/functions from
       sidekick-base Ty module), extract the name via the printer. *)
    let name = Format.asprintf "%a" Const.pp c in
    emit_str_const st t name

and emit_str_const (st : Twp_state.t) (t : Term.t) (name : string) : int =
  let ty_t = Term.ty t in
  let is_sort =
    match Term.view ty_t with
    | Term.E_type _ -> true
    | _ -> false
  in
  let safe_name = escape_name name in
  if is_sort then (
    emit_line st (Printf.sprintf "const %s [] E1" safe_name);
    let n = alloc_e st in
    emit_line st (Printf.sprintf "E%d const %s" n safe_name);
    n
  ) else (
    let ty_idx = emit_expr st ty_t in
    emit_line st (Printf.sprintf "const %s [] E%d" safe_name ty_idx);
    let n = alloc_e st in
    emit_line st (Printf.sprintf "E%d const %s" n safe_name);
    n
  )

(** Emit the E-index for a Lit.t.
    Positive: emit the term directly.
    Negative: represent as (t = false). *)
let emit_lit (st : Twp_state.t) (lit : Lit.t) : int =
  let t = Lit.term lit in
  let sign = Lit.sign lit in
  if sign then
    emit_expr st t
  else (
    let t_idx = emit_expr st t in
    let eq_bool_n = alloc_e st in
    emit_line st (Printf.sprintf "E%d const = E%d" eq_bool_n e_bool_idx);
    let eq_t_n = alloc_e st in
    emit_line st (Printf.sprintf "E%d app E%d E%d" eq_t_n eq_bool_n t_idx);
    let eq_t_false_n = alloc_e st in
    emit_line st
      (Printf.sprintf "E%d app E%d E%d" eq_t_false_n eq_t_n e_false_idx);
    eq_t_false_n
  )
