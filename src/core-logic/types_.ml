module H = CCHash

type const_view = ..

(** View of a level expression. *)
type level_view =
  | L_zero
  | L_succ of level
  | L_var of string  (** variable *)
  | L_max of level * level  (** max *)
  | L_imax of level * level  (** impredicative max. *)

and level = { l_view: level_view; mutable l_id: int }
(** A level expression *)

type term_view =
  | E_type of level
  | E_var of var
  | E_bound_var of bvar
  | E_const of const
  | E_app of term * term
  | E_app_fold of {
      f: term;  (** function to fold *)
      args: term list;  (** Arguments to the fold *)
      acc0: term;  (** initial accumulator *)
    }
  | E_lam of string * term * term
  | E_pi of string * term * term

and var = { v_name: string; v_ty: term }
and bvar = { bv_idx: int; bv_ty: term }
and const = { c_view: const_view; c_ops: const_ops; c_ty: term }

and const_ops = {
  pp: const_view Fmt.printer;  (** Pretty-print constant *)
  equal: const_view -> const_view -> bool;
      (** Equality of constant with any other constant *)
  hash: const_view -> int;  (** Hash constant *)
  ser: (term -> Ser_value.t) -> const_view -> string * Ser_value.t;
      (** Serialize a constant, along with a tag to recognize it. *)
}

and term = {
  view: term_view;
  (* computed on demand *)
  mutable ty: term_ty_;
  mutable id: int;
  (* contains: [highest DB var | 1:has free vars | 5:ctx uid] *)
  mutable flags: int;
}

and term_ty_ = T_ty of term | T_ty_delayed of (unit -> term)

module Term_ = struct
  let[@inline] equal (e1 : term) e2 : bool = e1 == e2
  let[@inline] hash (e : term) = H.int e.id
  let[@inline] compare (e1 : term) e2 : int = CCInt.compare e1.id e2.id
  let pp_debug_ : term Fmt.printer ref = ref (fun _ _ -> assert false)
end

module Var_ = struct
  let[@inline] equal v1 v2 =
    v1.v_name = v2.v_name && Term_.equal v1.v_ty v2.v_ty

  let[@inline] hash v1 = H.combine3 5 (H.string v1.v_name) (Term_.hash v1.v_ty)

  let compare a b : int =
    if Term_.equal a.v_ty b.v_ty then
      String.compare a.v_name b.v_name
    else
      compare a.v_ty b.v_ty

  module AsKey = struct
    type nonrec t = var

    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make (AsKey)
  module Set = CCSet.Make (AsKey)
  module Tbl = CCHashtbl.Make (AsKey)
end

type subst = { m: term Var_.Map.t } [@@unboxed]
