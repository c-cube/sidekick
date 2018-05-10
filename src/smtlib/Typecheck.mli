
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Loc = Locations

type 'a or_error = ('a, string) CCResult.t

(** {2 Parsing and Typing} *)

module Ctx : sig
  type t
  val create: unit -> t
  val pp : t CCFormat.printer
end

module PA = Parse_ast
module A = Sidekick_smt.Ast

val conv_term : Ctx.t -> PA.term -> A.term

val conv_statement : Ctx.t -> PA.statement -> A.statement list

