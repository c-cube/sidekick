
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

type term = Ast.term
type ty = Ast.Ty.t
type domain = ID.t list

type t = private {
  env: Ast.env;
  (* environment, defining symbols *)
  domains: domain Ast.Ty.Map.t;
  (* uninterpreted type -> its domain *)
  consts: term ID.Map.t;
  (* constant -> its value *)
}

(* TODO: remove *)
(** Trivial model *)
val empty : t

val make :
  env:Ast.env ->
  consts:term ID.Map.t ->
  domains:domain Ast.Ty.Map.t ->
  t

val pp : t CCFormat.printer

val eval : t -> term -> term

exception Bad_model of t * term * term
