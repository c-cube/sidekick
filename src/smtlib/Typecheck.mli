(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Loc = Smtlib_utils.V_2_6.Loc

type 'a or_error = ('a, string) CCResult.t

(** {2 Parsing and Typing} *)

module Ctx : sig
  type t
  val create: unit -> t
  val pp : t CCFormat.printer
end

module PA = Smtlib_utils.V_2_6.Ast
module A = Ast

val conv_term : Ctx.t -> PA.term -> A.term

val conv_statement : Ctx.t -> PA.statement -> A.statement list

