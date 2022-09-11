# Sidekick

This is a guide to using Sidekick and to implementing custom SMT solvers.

## Quickstart

You will need [opam](http://opam.ocaml.org) and a relatively recent version
of OCaml. I'd recommend OCaml 4.11, even though versions as old as 4.04 are
supported.
Using [merlin](https://github.com/ocaml/merlin)
or [ocaml-lsp](https://github.com/ocaml/ocaml-lsp) in your editor is
strongly recommended, to help exploring the API and to get fast feedback
on mistakes.

The API documentation can be [found online](https://c-cube.github.io/sidekick/).

Clone this repository:

```
$ git clone https://github.com/c-cube/sidekick.git
$ cd sidekick
```

Then create a local switch (much simpler in the long run). This will take a
little while as it compiles OCaml.

```
$ opam sw create . 4.11.0
```

Let's test that sidekick is installed. In an ocaml toplevel (just run `ocaml`),
type the first three lines (without the leading `#`, which indicates the
OCaml prompt):

```ocaml
# #use "topfind";;
# #require "sidekick-base";;
# #show Sidekick_base;;
module Sidekick_base :
  sig
    module Types_ = Sidekick_base__.Types_
...
  end
```

This should print the interface of the `Sidekick_base` library.

For real work it's better to create a new project
(e.g. using `dune init executable <some name>`), have it depend on sidekick,
and write your own SMT solver in this project by compiling it to native code.
Here we use the toplevel because it is interactive, and because it helps
me write this guide.

## The basics

First, let us reiterate, as [in the README](https://github.com/c-cube/sidekick#short-summary)
that there are several libraries in this project.
We're going to use these libraries:

- `sidekick`: definition of algorithms, data-structures, solvers, and decision
  procedures for SMT solvers.
  This is almost entirely _functorized_, which means that the component
  are parametrized as much as possible so as to be agnostic to how
  precisely terms, formulas, clauses, etc. are implemented.

  One can use this library directly, but it means providing an
  implementation to each functor, which can be sometimes intricate.

- `sidekick-base`: a fixed definition of terms, types, statements, etc. that
  is compatible with `sidekick`.
  This gives you a starting point to manipulate logic formulas and
  use SMT on them.

  The sublibrary `sidekick-base.solver` provides an instance of the
  main Solver, along with a few theories. Let us peek into it now:

```ocaml
# #require "sidekick-base";;
# #show Sidekick_base.Solver;;
module Solver = Sidekick_base__.Solver
module Solver = Sidekick_base.Solver
module Solver :
  sig
    type t = Solver.t
...
```

Let's bring more all these things into scope, and install some printers
for legibility:

```ocaml
# open Sidekick_core;;
# open Sidekick_base;;
# open Sidekick_smt_solver;;
# #install_printer Term.pp;;
# #install_printer Lit.pp;;
# #install_printer Ty.pp;;
# #install_printer Const.pp;;
# #install_printer Model.pp;;
```

## First steps in solving

To solve a formula, we need to first create some terms and a solver.

### Manipulating terms

We're going to need a _term store_.
All terms in sidekick live in a store, which is necessary for _hashconsing_
(and could be used for more data-oriented representation of terms
 in alternative implementations.)

```ocaml
# let tstore = Term.Store.create ();;
val tstore : Term.store = <abstr>

# Term.Store.size tstore;;
- : int = 0
```

Let's look at some basic terms we can build immediately.

```ocaml
# Term.true_ tstore;;
- : Term.term = true

# Term.false_ tstore;;
- : Term.term = false

# Term.eq tstore (Term.true_ tstore) (Term.false_ tstore);;
- : Term.term = (= Bool true false)
```

Cool. Similarly, we need to manipulate types.

`Sidekick_base` the type store is merely `unit` because we just use a global
hashconsing state for types.
In general we'd need to carry around a type store as well.
The only predefined type is _bool_, the type of booleans:

```ocaml
# Ty.bool tstore;;
- : Term.term = Bool
```

Now we can define new terms and constants. Let's try to define
a few boolean constants named "p", "q", "r":

```ocaml
# let p = Uconst.uconst_of_str tstore "p" [] @@ Ty.bool tstore;;
val p : Term.term = p
# let q = Uconst.uconst_of_str tstore "q" [] @@ Ty.bool tstore;;
val q : Term.term = q
# let r = Uconst.uconst_of_str tstore "r" [] @@ Ty.bool tstore;;
val r : Term.term = r

# Term.ty p;;
- : Term.term = Bool

# Term.equal p q;;
- : bool = false

# Term.view p;;
- : Term.view = Sidekick_base.Term.E_const p

# Term.equal p p;;
- : bool = true
```

We can now build formulas from these.

```ocaml
# let p_eq_q = Term.eq tstore p q;;
val p_eq_q : Term.term = (= Bool p q)

# let p_imp_r = Form.imply tstore p r;;
val p_imp_r : Term.term = (=> p r)
```

### Using a solver.

We can create a solver by passing `Solver.create` a term store
and a proof trace (here, `Proof_trace.dummy` because we don't care about
proofs).
A list of theories can be added initially, or later using
`Solver.add_theory`.

```ocaml
# let proof = Proof_trace.dummy;;
val proof : Proof_trace.t = <abstr>
# let solver = Solver.create_default ~theories:[th_bool_static] ~proof tstore ();;
val solver : solver = <abstr>

# Solver.add_theory;;
- : solver -> theory -> unit = <fun>
```

Alright, let's do some solving now ⚙️. We're going to assert
several formulas and check satisfiability in between each.

We start with `p = q`.
 
```ocaml
# p_eq_q;;
- : Term.term = (= Bool p q)
# Solver.assert_term solver p_eq_q;;
- : unit = ()
# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_smt_solver.Solver.Sat
 (model
  (false := false)
  (q := true)
  ((box (= Bool p q)) := true)
  (true := true)
  (p := true))
```

It is satisfiable, and we got a model where "p" and "q" are both false.
We also get an internal term `_tseitin_equiv_0` in the model, which is
produced by the theory of boolean when it encoded the equivalence.

We can also ask Sidekick to check satisfiability _under assumptions_,
meaning we temporarily add some hypotheses to the solver and check
whether the assertions and hypotheses are satisfiable together.

```ocaml
# Solver.solve solver
    ~assumptions:[Solver.mk_lit_t solver p;
                  Solver.mk_lit_t solver q ~sign:false];;
- : Solver.res =
Sidekick_smt_solver.Solver.Unsat
 {Sidekick_smt_solver.Solver.unsat_core = <fun>; unsat_step_id = <fun>}
```

Here it's unsat, because we asserted "p = q", and then assumed "p"
to be true and "q" to be false.
Deconstructing the result further, we could obtain an _unsat core_
(a subset of the assumptions sufficient to explain the unsatisfiability),
or a _proof_ (to check the unsatisfiability result somehow).

Note that this doesn't affect satisfiability without assumptions:

```ocaml
# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_smt_solver.Solver.Sat
 (model
  (false := false)
  (q := true)
  ((box (= Bool p q)) := true)
  (true := true)
  (p := true))
```

We can therefore add more formulas and see where it leads us.

```ocaml
# p_imp_r;;
- : Term.term = (=> p r)
# Solver.assert_term solver p_imp_r;;
- : unit = ()
# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_smt_solver.Solver.Sat
 (model
  (false := false)
  (q := true)
  ((box (= Bool p q)) := true)
  (r := true)
  ((box (or r (not p) false)) := true)
  (true := true)
  (p := true))
```

Still satisfiable, but now we see `r` in the model, too. And now:

```ocaml
# let q_imp_not_r = Form.imply tstore q (Form.not_ tstore r);;
val q_imp_not_r : Term.term = (=> q (not r))
# Solver.assert_term solver q_imp_not_r;;
- : unit = ()

# Solver.assert_term solver p;;
- : unit = ()

# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_smt_solver.Solver.Unsat
 {Sidekick_smt_solver.Solver.unsat_core = <fun>; unsat_step_id = <fun>}
```

This time we got _unsat_ and there is no way of undoing it.
It comes from the fact that `p=q`, but `p` and `q` imply contradictory
formulas (`r` and `¬r`), so when we force `p` to be true, `q` is true too
and the contradiction is triggered.

## A bit of arithmetic

We can solve linear real arithmetic problems as well.
Let's create a new solver and add the theory of reals to it.

```ocaml
# let solver = Solver.create_default ~theories:[th_bool_static; th_lra] ~proof tstore ();;
val solver : solver = <abstr>
```

Create a few arithmetic constants.

```ocaml
# let real = Ty.real tstore;;
val real : Term.term = Real
# let a = Uconst.uconst_of_str tstore "a" [] real;;
val a : Term.term = a
# let b = Uconst.uconst_of_str tstore "b" [] real;;
val b : Term.term = b

# Term.ty a;;
- : Term.term = Real

# let a_leq_b = LRA_term.leq tstore a b;;
val a_leq_b : Term.term = (<= a b)
```

We can play with assertions now:

```ocaml
# Solver.assert_term solver a_leq_b;;
- : unit = ()
# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_smt_solver.Solver.Sat
 (model
  (b := 0)
  (false := false)
  ((box (<= (+ a ((* -1) b)) 0)) := true)
  ($_le_comb[0] := 0)
  (a := 0)
  (true := true))


# let a_geq_1 = LRA_term.geq tstore a (LRA_term.const tstore (Q.of_int 1));;
val a_geq_1 : Term.term = (>= a 1)
# let b_leq_half = LRA_term.(leq tstore b (LRA_term.const tstore (Q.of_string "1/2")));;
val b_leq_half : Term.term = (<= b 1/2)

# let res = Solver.solve solver
    ~assumptions:[Solver.mk_lit_t solver p;
                  Solver.mk_lit_t solver a_geq_1;
                  Solver.mk_lit_t solver b_leq_half];;
val res : Solver.res =
  Sidekick_smt_solver.Solver.Unsat
   {Sidekick_smt_solver.Solver.unsat_core = <fun>; unsat_step_id = <fun>}

# match res with Solver.Unsat {unsat_core=us; _} -> us() |> Iter.to_list | _ -> assert false;;
- : Proof_trace.lit list = [[[ (>= a 1) ]]; [[ (<= b 1/2) ]]]
```

This just showed that `a=1, b=1/2, a>=b` is unsatisfiable.
The junk assumption `p` was not used during the proof
and therefore doesn't appear in the unsat core we extract from `res`;
the assertion `a<=b` isn't in the core either because it was asserted
using `(assert …)` rather than passed as a local assumption,
so it's "background" knowledge.

## Functions and congruence closure

We can define function symbols, not just constants. Let's also define `u`,
an uninterpreted type.

```ocaml
# let u = Ty.uninterpreted_str tstore "u";;
val u : Term.term = u

# let u1 = Uconst.uconst_of_str tstore "u1" [] u;;
val u1 : Term.term = u1
# let u2 = Uconst.uconst_of_str tstore "u2" [] u;;
val u2 : Term.term = u2
# let u3 = Uconst.uconst_of_str tstore "u3" [] u;;
val u3 : Term.term = u3

# let f1 = Uconst.uconst_of_str tstore "f1" [u] u;;
val f1 : Term.term = f1
# Term.view f1;;
- : Term.view = Sidekick_base.Term.E_const f1

# let f1_u1 = Term.app_l tstore f1 [u1];;
val f1_u1 : Term.term = (f1 u1)

# Term.ty f1_u1;;
- : Term.term = u
# Term.view f1_u1;;
- : Term.view = Sidekick_base.Term.E_app (f1, u1)
```

Anyway, Sidekick knows how to reason about functions.

```ocaml
# let solver = Solver.create_default ~theories:[] ~proof tstore ();;
val solver : solver = <abstr>

# (* helper *)
  let appf1 x = Term.app_l tstore f1 x;;
val appf1 : Term.term list -> Term.term = <fun>

# Solver.assert_term solver (Term.eq tstore u2 (appf1 [u1]));;
- : unit = ()
# Solver.assert_term solver (Term.eq tstore u3 (appf1 [u2]));;
- : unit = ()
# Solver.assert_term solver (Term.eq tstore u1 (appf1 [appf1 [u1]]));;
- : unit = ()
# Solver.assert_term solver
  (Term.eq tstore u1 (appf1 [appf1 [appf1 [u1]]]));;
- : unit = ()

# Solver.solve solver
    ~assumptions:[Solver.mk_lit_t solver ~sign:false (Term.eq tstore u1 (appf1[u1]))];;
- : Solver.res =
Sidekick_smt_solver.Solver.Unsat
 {Sidekick_smt_solver.Solver.unsat_core = <fun>; unsat_step_id = <fun>}

# Solver.solve solver
    ~assumptions:[Solver.mk_lit_t solver ~sign:false (Term.eq tstore u2 u3)];;
- : Solver.res =
Sidekick_smt_solver.Solver.Unsat
 {Sidekick_smt_solver.Solver.unsat_core = <fun>; unsat_step_id = <fun>}
```

Assuming: `f1(u1)=u2, f1(u2)=u3, f1^2(u1)=u1, f1^3(u1)=u1`,
we proved that `f1(u1)=u1`, then that `u2=u3` because both are equal to `u1`.

## Extending sidekick

The most important function here is `Solver.add_theory`
(or the `~theories` argument to `Solver.create`).
It means one can just implement a new theory in the same vein as the existing
ones and add it to the solver.
Note that the theory doesn't _need_ to be functorized, it could directly
work on the term representation you use (or `Sidekick_base.Term` if you
reuse that).

The API for theories is found [here](https://c-cube.github.io/sidekick/dev/sidekick/Sidekick_core/module-type-SOLVER/module-type-THEORY/index.html).
In addition to using terms, types, etc. it has access to
a [Solver_internal.t](https://c-cube.github.io/sidekick/dev/sidekick/Sidekick_core/module-type-SOLVER/Solver_internal/index.html#type-t) object, which contains the internal API
of the SMT solver. The internal solver allows a theory to do many  things, including:

- propagate literals
- raise conflicts (add a lemma which contradicts the current candidate model)
- create new literals
- hook into the central [Congruence Closure](https://c-cube.github.io/sidekick/dev/sidekick/Sidekick_core/module-type-CC_S/index.html)
- register preprocessing functions (typically, to transform some constructs
  into clauses)
- register simplification functions


TODO: extending terms

TODO: basic custom theory (enums?)

`
