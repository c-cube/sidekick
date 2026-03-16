(** State for emitting .twp proof files.

    Indices:
    - E<n> = expression (type, term, etc.)
    - P<n> = proof step
    - Q<n> = sequent

    After the preamble the following E-indices are fixed:
      E1 = type
      E2 = bool
      E3 = false
      E4 = type variable A (for polymorphic =)
      E5 = A -> bool
      E6 = A -> A -> bool   (type of =)

    Subsequent E-indices are allocated on demand.
*)

open Sidekick_core

type t = {
  buf : Buffer.t;
  (* maps term id → E-index *)
  term_tbl : int Term.Tbl.t;
  (* maps step id → P-index *)
  step_tbl : (int, int) Hashtbl.t;
  mutable next_e : int;
  mutable next_p : int;
  mutable next_q : int;
}

(* Fixed E-indices from the preamble *)
let e_type = 1
let e_bool = 2
let e_false = 3
let _e_tyvar_a = 4
let _e_a_arrow_bool = 5
let _e_eq_ty = 6  (* A -> A -> bool, the type of = *)

let create () : t =
  {
    buf = Buffer.create 4096;
    term_tbl = Term.Tbl.create 64;
    step_tbl = Hashtbl.create 64;
    next_e = 7;   (* E1-E6 reserved by preamble *)
    next_p = 1;
    next_q = 1;
  }

let emit_line (self : t) (line : string) : unit =
  Buffer.add_string self.buf line;
  Buffer.add_char self.buf '\n'

let alloc_e (self : t) : int =
  let n = self.next_e in
  self.next_e <- n + 1;
  n

let alloc_p (self : t) : int =
  let n = self.next_p in
  self.next_p <- n + 1;
  n

let alloc_q (self : t) : int =
  let n = self.next_q in
  self.next_q <- n + 1;
  n

(** Emit the fixed preamble that every .twp file needs.
    Declares bool, false, and the polymorphic = constant. *)
let emit_preamble (self : t) : unit =
  emit_line self "# preamble: bool, false, polymorphic =";
  emit_line self "E1 type";
  emit_line self "const bool [] E1";
  emit_line self "E2 const bool";
  emit_line self "const false [] E2";
  emit_line self "E3 const false";
  (* type variable A : type *)
  emit_line self "E4 var A E1";
  (* A -> bool *)
  emit_line self "E5 arrow E4 E2";
  (* A -> A -> bool *)
  emit_line self "E6 arrow E4 E5";
  (* const = [A] (A -> A -> bool) *)
  emit_line self "const = [A] E6"

let buffer (self : t) : Buffer.t = self.buf
