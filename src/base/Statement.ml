open Types_

type t = statement =
  | Stmt_set_logic of string
  | Stmt_set_option of string list
  | Stmt_set_info of string * string
  | Stmt_data of data list
  | Stmt_ty_decl of { name: ID.t; arity: int; ty_const: ty }
      (** new atomic cstor *)
  | Stmt_decl of { name: ID.t; ty_args: ty list; ty_ret: ty; const: term }
  | Stmt_define of definition list
  | Stmt_assert of term
  | Stmt_assert_clause of term list
  | Stmt_check_sat of (bool * term) list
  | Stmt_get_model
  | Stmt_get_value of term list
  | Stmt_exit

(** Pretty print a statement *)
let pp out = function
  | Stmt_set_logic s -> Fmt.fprintf out "(set-logic %s)" s
  | Stmt_set_option l ->
    Fmt.fprintf out "(@[set-logic@ %a@])" (Util.pp_list Fmt.string) l
  | Stmt_set_info (a, b) -> Fmt.fprintf out "(@[set-info@ %s@ %s@])" a b
  | Stmt_check_sat [] -> Fmt.string out "(check-sat)"
  | Stmt_check_sat l ->
    let pp_pair out (b, t) =
      if b then
        Term.pp_debug out t
      else
        Fmt.fprintf out "(@[not %a@])" Term.pp_debug t
    in
    Fmt.fprintf out "(@[check-sat-assuming@ (@[%a@])@])" (Fmt.list pp_pair) l
  | Stmt_ty_decl { name; arity; ty_const = _ } ->
    Fmt.fprintf out "(@[declare-sort@ %a %d@])" ID.pp name arity
  | Stmt_decl { name; ty_args; ty_ret; const = _ } ->
    Fmt.fprintf out "(@[<1>declare-fun@ %a (@[%a@])@ %a@])" ID.pp name
      (Util.pp_list Ty.pp) ty_args Ty.pp ty_ret
  | Stmt_assert t -> Fmt.fprintf out "(@[assert@ %a@])" Term.pp_debug t
  | Stmt_assert_clause c ->
    Fmt.fprintf out "(@[assert-clause@ %a@])" (Util.pp_list Term.pp_debug) c
  | Stmt_exit -> Fmt.string out "(exit)"
  | Stmt_data l ->
    Fmt.fprintf out "(@[declare-datatypes@ %a@])" (Util.pp_list Data_ty.pp) l
  | Stmt_get_model -> Fmt.string out "(get-model)"
  | Stmt_get_value l ->
    Fmt.fprintf out "(@[get-value@ (@[%a@])@])" (Util.pp_list Term.pp_debug) l
  | Stmt_define _ -> assert false
(* TODO *)
