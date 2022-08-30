include Sidekick_core

(* FIXME
   module Proof_ser = Sidekick_base_proof_trace.Proof_ser
   module Storage = Sidekick_base_proof_trace.Storage
*)

type term = Term.t
type ty = Term.t
type value = Term.t

type uconst = { uc_id: ID.t; uc_ty: ty }
(** Uninterpreted constant. *)

type ty_view =
  | Ty_int
  | Ty_real
  | Ty_uninterpreted of { id: ID.t; mutable finite: bool }
(* TODO: remove (lives in Data_ty now)
   | Ty_data of { data: data }
*)

and data = {
  data_id: ID.t;
  data_cstors: cstor ID.Map.t lazy_t;
  data_as_ty: ty lazy_t;
}

and cstor = {
  cstor_id: ID.t;
  cstor_is_a: ID.t;
  mutable cstor_arity: int;
  cstor_args: select list lazy_t;
  cstor_ty_as_data: data;
  cstor_ty: ty lazy_t;
}

and select = {
  select_id: ID.t;
  select_cstor: cstor;
  select_ty: ty lazy_t;
  select_i: int;
}

(* FIXME: just use  terms; introduce a Const.view for V_element
   (** Semantic values, used for models (and possibly model-constructing calculi) *)
   type value_view =
     | V_element of { id: ID.t; ty: ty }
         (** a named constant, distinct from any other constant *)
     | V_cstor of { c: cstor; args: value list }
     | V_custom of {
         view: value_custom_view;
         pp: value_custom_view Fmt.printer;
         eq: value_custom_view -> value_custom_view -> bool;
         hash: value_custom_view -> int;
       }  (** Custom value *)
     | V_real of Q.t

   and value_custom_view = ..
*)

type definition = ID.t * ty * term

type statement =
  | Stmt_set_logic of string
  | Stmt_set_option of string list
  | Stmt_set_info of string * string
  | Stmt_data of data list
  | Stmt_ty_decl of ID.t * int (* new atomic cstor *)
  | Stmt_decl of ID.t * ty list * ty
  | Stmt_define of definition list
  | Stmt_assert of term
  | Stmt_assert_clause of term list
  | Stmt_check_sat of (bool * term) list
  | Stmt_get_model
  | Stmt_get_value of term list
  | Stmt_exit
