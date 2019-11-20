(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Loc = Smtlib_utils.V_2_6.Loc
module PA = Smtlib_utils.V_2_6.Ast
module T = Sidekick_base_term.Term
module Stmt = Sidekick_base_term.Statement

type 'a or_error = ('a, string) CCResult.t

(** {2 Parsing and Typing} *)

module Ctx : sig
  type t
  val create: T.state -> t
end

val conv_term : Ctx.t -> PA.term -> T.t

val conv_statement : Ctx.t -> PA.statement -> Stmt.t list

