(** Emit terms in traces.

  Traces will contains terms, encoded as a DAG. Each subterm is its own
  event, and gets a term identifier used in other subsequent entries
  to refer to it.
*)

open Sidekick_core_logic
module Tr = Sidekick_trace

type term_ref = private Tr.entry_id

type Tr.entry_view +=
  private
  | T_ty of int
  | T_app of term_ref * term_ref
  | T_var of string * term_ref
  | T_bvar of int * term_ref
  | T_const of { c: Const.view; c_ops: Const.Ops.t; ty: term_ref }
  | T_lam of { v_name: string; v_ty: term_ref; body: term_ref }
  | T_pi of { v_name: string; v_ty: term_ref; body: term_ref }
  (* FIXME: remove *)
  [@@ocaml.warning "-38"]

type t

val create : sink:Tr.Sink.t -> unit -> t
val emit : t -> Term.t -> term_ref
val emit' : t -> Term.t -> unit

(* TODO
   val reader : Term.store -> Tr.Entry_read.reader
*)
