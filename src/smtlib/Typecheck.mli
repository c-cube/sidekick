(** Typing AST *)

module Loc = Smtlib_utils.V_2_6.Loc
module PA = Smtlib_utils.V_2_6.Ast
module T = Sidekick_base.Term
module Stmt = Sidekick_base.Statement

type 'a or_error = ('a, string) CCResult.t

(** {2 Type-checking and type inference} *)

(** Typing context *)
module Ctx : sig
  type t

  val set_default_num_real : t -> unit
  val set_default_num_int : t -> unit
  val create : T.store -> t
end

(** {2 Conversion from smtlib-utils} *)

val conv_term : Ctx.t -> PA.term -> T.t
val conv_statement : Ctx.t -> PA.statement -> Stmt.t list
