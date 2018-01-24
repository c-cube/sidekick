
## CC with eval

evaluation should be based on a form of conditional rewriting for first-order
symbols.

### Terms

Roughly:

```ocaml
type t = {
  id: int;
  ty: ty;
  repr: ty_repr;
}
and ty_repr =
  | App of cst * t array
  | Custom of {
    view: term_view;
    tc: term_tc;
  } (** Custom theory stuff (e.g. LRA polynomial) *)

(* typeclass for evaluation *)
and term_tc = {
  t_pp : term_view printer;
  t_map : (t -> t) -> term_view -> term_view;
  t_children : term_view -> t Bag.t;
  t_equal : term_view -> term_view -> bool;
  t_hash : term_view -> int;
}

and term_view = ..
```

Constants and types are also extensible:


```ocaml
type ty = {
  ty_id : int;
  ty_repr: ty_repr;
}
and ty_repr =
  | Bool
  | Arrow of ty list * ty
  | Var of db
  | Forall of ty (* polymorphic type *)
  | Ty_custom of {
    view: ty_view;
    tc: ty_tc
  } (** Extensible case *)
and ty_tc = {
  ty_pp : term_view printer;
  ty_equal : term_view -> term_view -> bool;
  ty_hash : term_view -> int;
}
and ty_view = ..
```

and

```ocaml
type cst = {
  cst_id: ID.t;
  cst_ty: Ty.t;
  cst_decl: decl_view;
  cst_rules: rule list;
  cst_fields: Fields.t;
  (* assoc, comm, injective, etc? *)
}

(** Per-theory custom info for the constant *)
and decl_view = ..

(** A rewrite rule *)
and rule = {
  r_guards: decl_view -> args:t array -> Lit.t list;
  r_rhs: decl_view -> args:term array -> term;
}

```

### Example : ite

If-then-else (`ite`) would be a special constant of type `Πα. bool -> α → α → α`
and two rules:

```ocaml
[ {r_guards=(fun _ [cond;_;_] -> [Lit.of_term cond]);
   r_rhs=(fun _ [_;a;_] -> a);
  };
  {r_guards=(fun _ [cond;_;_] -> [Lit.neg @@ Lit.of_term cond]);
   r_rhs=(fun _ [_;_;b] -> b);
  };
]
```

The first rule will fire if `cond` is true, and reduce `(ite cond a b)` into `a`;
the second rule fires if `¬cond` is true, and reduces to `b`.

Rules should be pairwise exclusive (i.e. the conjunction of guards of
any two rules must be unsat)

### Congruence closure

Classic CC with additional support for injectivity, etc.

- injectivity based on flag on `cst` heads
- mutual exclusion of constructors (for datatypes)
- → need notion of "value" (extensible, per theory/per type)
    such as at most one value per equiv. class, and values *never* reduce.
- notion of relevancy for evaluation (and SAT literals).
  E.g. in `ite cond a b`, only `cond` is relevant. `a` and `b` only become
  relevant when the term reduces to either of them.
  → also allows control of evaluation under datatypes
  (in `S(n)`, `n` can only become relevant if a projection/match/function call
   brings it into a relevant context by removing `S` ⇒ emulate WHNF)

Given a *relevant* node of the CC, of the form `f t1…tn`, where `f` has evaluation
rules:

- we instantiate all literals in the guards of the rules (to know which
  rule applies).
- if all literals in the guard of one of the rules applies, then the rule
  fires.
  * We *replace* `f t1…tn` by RHS of the rule applied
    to `f` and `repr(t1)…repr(tn)`, and flag `f t1…tn` as masked.
  * It remains in the equivalence class, but points directly to its new
    normal form and should not participate in regular congruence checking.
  * Upon backtrack (as soon as the guard is not true anymore) we restore
    the old term and make it active again.

It's very important that, in a long chain of reduction `t1 → t2 → … → tn`,
only `tn` is active and the other terms are only there to provide explanations
but do not cost any complexity during CC.

