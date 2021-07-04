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
    module Base_types = Sidekick_base__.Base_types
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

- `sidekick_base`: a fixed definition of terms, types, statements, etc. that
  is compatible with `sidekick`.
  This gives you a starting point to manipulate logic formulas and
  use SMT on them.

  The sublibrary `sidekick-base.solver` provides an instance of the
  main Solver, along with a few theories. Let us peek into it now:

```ocaml
# #require "sidekick-base.solver";;
# #show Sidekick_base_solver;;
module Sidekick_base_solver :
  sig
    module Solver_arg : sig ... end
    module Solver : sig ... end
    module Th_data : sig ... end
    module Th_bool : sig ... end
    module Th_lra : sig ... end
    val th_bool : Solver.theory
    val th_data : Solver.theory
    val th_lra : Solver.theory
  end
```

Let's bring more all these things into scope, and install some printers
for legibility:

```ocaml
# open Sidekick_base;;
# open Sidekick_base_solver;;
# #install_printer Term.pp;;
# #install_printer Ty.pp;;
# #install_printer Fun.pp;;
# #install_printer Model.pp;;
# #install_printer Solver.Model.pp;;
# #install_printer Proof.pp_debug;;
Proof.pp_debug has a wrong type for a printing function.
```

## First steps in solving

To solve a formula, we need to first create some terms and a solver.

### Manipulating terms

We're going to need a _term store_.
All terms in sidekick live in a store, which is necessary for _hashconsing_
(and could be used for more data-oriented representation of terms
 in alternative implementations.)

```ocaml
# let tstore = Term.create ();;
val tstore : Term.store = <abstr>

# Term.store_size tstore;;
- : int = 2
```

Interesting, there are already two terms that are predefined.
Let's peek at them:

```ocaml
# let all_terms_init =
    Term.store_iter tstore |> Iter.to_list |> List.sort Term.compare;;
val all_terms_init : Term.t list = [true; false]

# Term.true_ tstore;;
- : Term.t = true

# (* check it's the same term *)
  Term.(equal (true_ tstore) (List.hd all_terms_init));;
- : bool = true

# Term.(equal (false_ tstore) (List.hd all_terms_init));;
- : bool = false
```

Cool. Similarly, we need to manipulate types.

`Sidekick_base` the type store is merely `unit` because we just use a global
hashconsing state for types.
In general we'd need to carry around a type store as well.
The only predefined type is _bool_, the type of booleans:

```ocaml
# Ty.bool ();;
- : Ty.t = Bool
```

Now we can define new terms and constants. Let's try to define
a few boolean constants named "p", "q", "r":

```ocaml
# let p = Term.const_undefined_const tstore (ID.make "p") @@ Ty.bool();;
val p : Term.t = p
# let q = Term.const_undefined_const tstore (ID.make "q") @@ Ty.bool();;
val q : Term.t = q
# let r = Term.const_undefined_const tstore (ID.make "r") @@ Ty.bool();;
val r : Term.t = r

# Term.ty p;;
- : Ty.t = Bool

# Term.equal p q;;
- : bool = false

# Term.view p;;
- : Term.t Term.view = Sidekick_base.Term.App_fun (p/3, [||])

# Term.store_iter tstore |> Iter.to_list |> List.sort Term.compare;;
- : Term.t list = [true; false; p; q; r]
```

We can now build formulas from these.

```ocaml
# let p_eq_q = Term.eq tstore p q;;
val p_eq_q : Term.t = (= p q)

# let p_imp_r = Form.imply tstore p r;;
val p_imp_r : Term.t = (=> r p)
```

### Creating a solver.

We can create a solver by passing `Solver.create` a term store
and a type store (which in our case is simply `() : unit`).
A list of theories can be added initially, or later using
`Solver.add_theory`.

```ocaml
# let solver = Solver.create ~theories:[th_bool] tstore () ();;
val solver : Solver.t = <abstr>

# Solver.add_theory;;
- : Solver.t -> Solver.theory -> unit = <fun>
```

Alright, let's do some solving now ⚙️. We're going to assert
several formulas and check satisfiability in between each.

We start with `p = q`.
 
```ocaml
# p_eq_q;;
- : Term.t = (= p q)
# Solver.assert_term solver p_eq_q;;
- : unit = ()
# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_base_solver.Solver.Sat
 (model
  (true := true)
  (false := false)
  (p := false)
  (q := false)
  (_tseitin_equiv_0 := true))
```

It is satisfiable, and we got a model where "p" and "q" are both false.
We also get an internal term `_tseitin_equiv_0` in the model, which is
produced by the theory of boolean when it encoded the equivalence.

We can also ask Sidekick to check satisfiability _under assumptions_,
meaning we temporarily add some hypotheses to the solver and check
whether the assertions and hypotheses are satisfiable together.

```ocaml
# Solver.solve solver
    ~assumptions:[Solver.mk_atom_t' solver p;
                  Solver.mk_atom_t' solver q ~sign:false];;
- : Solver.res =
Sidekick_base_solver.Solver.Unsat
 {Sidekick_base_solver.Solver.proof = <lazy>; unsat_core = <lazy>}
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
Sidekick_base_solver.Solver.Sat
 (model
  (true := true)
  (false := false)
  (p := false)
  (q := false)
  (_tseitin_equiv_0 := true))
```

We can therefore add more formulas and see where it leads us.

```ocaml
# p_imp_r;;
- : Term.t = (=> r p)
# Solver.assert_term solver p_imp_r;;
- : unit = ()
# Solver.solve ~assumptions:[] solver;;
- : Solver.res =
Sidekick_base_solver.Solver.Sat
 (model
  (true := true)
  (false := false)
  (p := false)
  (q := false)
  (r := false)
  (_tseitin_equiv_0 := true)
  (_tseitin_implies_1 := true))
```

Still satisfiable, but now we see `r` in the model, too. And now:

```ocaml
# let q_imp_not_r = Form.imply tstore q (Form.not_ tstore r);;
# Solver.assert_term solver q_imp_not_r;;

# Solver.assert_term solver p;;

# Solver.solve ~assumptions:[] solver;;
```

This time we got _unsat_ and there is no way of undoing it.
It comes from the fact that `p=q`, but `p` and `q` imply contradictory
formulas (`r` and `¬r`), so when we force `p` to be true, `q` is true too
and the contradiction is triggered.
