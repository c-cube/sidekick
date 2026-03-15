val whnf : ?cache:Term.t Term.Tbl.t -> Term.store -> Term.t -> Term.t
(** [whnf store e] reduces [e] to weak head normal form by beta-reducing at the
    head until stuck. The optional [cache] is a memoisation table; pass the same
    table across calls to amortise work over a DAG. *)

val def_eq : Term.store -> Term.t -> Term.t -> bool
(** [def_eq store a b] is true iff [a] and [b] are definitionally equal: both
    sides are reduced to WHNF and then compared structurally, using
    [Level.judge_eq] for universe levels. Results are memoised internally on the
    shared DAG structure.

    Note: this is installed as the kernel's equality check
    ([Term.Internal_.def_eq_ref]) when this module is loaded. *)
