(** Statements.

    A statement is an instruction for the SMT solver to do something,
    like asserting that a formula is true, declaring a new constant,
    or checking satisfiabilty of the current set of assertions. *)

open Types_

type t = statement =
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

include Sidekick_sigs.PRINT with type t := t
