# Guarded Interaction Trees

This is the Coq formalization of guarded interaction trees augmented with context-dependent effects and preemptive concurrency, associated examples and case studies.

## Installation instructions

To install the formalization you will need Iris and std++ libraries.

- with [opam](https://opam.ocaml.org/doc/Install.html):
  ```
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam update
  eval $(opam env)
  opam install . --deps-only
  ```
- with [nix (flake enabled)](https://nixos.org/download.html):
  ```
  nix develop
  ```

Then the formalization can be compiled with `make` and installed with
`make install`. You can pass the additional parameters to compile the
formalization using multiple cores, e.g. `make -j 3` for compiling
using 3 threads.

## Typechecking the development
- ```make all``` --- typecheck the project.
- ```./check_admits.sh``` --- count used admits.
- ```./check_axioms.sh``` --- count declared axioms.

## Intro

[Intro notes](./INTRO.md)

## Code Overview

All the code lives in the `theories` folder. Below is the quick guide
to the code structure.

For the representation of binders we use a library implemented by
Filip Sieczkowski and Piotr Polesiuk, located in the `vendor/Binding/`
folder.

```
.
+-- vendor/Binding/ (substitution framework)
+-- theories/
|   +-- effects/ (concrete effects, their semantics, and program logic rules)
|   |   +-- callcc.v (call/cc and throw)
|   |   +-- delim.v (shift and reset)
|   |   +-- store.v (alloc, dealloc, write, read, generic atomic read-modify, and concrete instances: CAS, XCHG, FAA)
|   |   +-- io_tape.v
|   |   +-- coroutines.v (asymmetric coroutines)
|   |   +-- fork.v (preemptive concurrency)
|   +-- hom.v (homomorphisms packaged as sigma-types)
|   +-- examples/
|   |   +-- delim_lang/ (formalization of the language with shift/reset and its soundness/adequacy wrt abstract machine semantics)
|   |   |   +-- example.v (program logic reasoning example for denotations that contain shift/reset)
|   |   |   +-- glue.v (formalization of the language with heap, type safety of the language interoperability)
|   |   |   +-- hom.v (homomorphisms specific to delim lang)
|   |   |   +-- interp.v (denotation semantics and soundness)
|   |   |   +-- lang.v (calculus)
|   |   |   +-- logpred.v (unary logical relation)
|   |   |   +-- logrel.v (binary logical relation, adequacy)
|   |   |   +-- typing.v (typing rules)
|   |   +-- lang_callcc/ (formalization of the language with throw and call/cc, the soundness and adequacy)
|   |   |   +-- hom.v (homomorphisms specific to lang callcc)
|   |   |   +-- interp.v (denotation semantics and soundness)
|   |   |   +-- lang.v (calculus)
|   |   |   +-- logrel.v (binary logical relation, adequacy)
|   |   +-- input_lang_callcc/ (formalization of the language with io, throw and call/cc, the soundness and adequacy)
|   |   |   +-- hom.v (homomorphisms specific to input lang callcc)
|   |   |   +-- interp.v (denotation semantics and soundness)
|   |   |   +-- lang.v (calculus)
|   |   |   +-- logrel.v (binary logical relation, adequacy)
|   |   +-- input_lang/ (ported formalization of the language with io, the soundness and adequacy)
|   |   |   +-- interp.v
|   |   |   +-- lang.v
|   |   |   +-- logpred.v
|   |   |   +-- logrel.v
|   |   +-- affine_lang/ (ported formalization of the affine language, type safety of the language interoperability)
|   |   |   +-- lang.v
|   |   |   +-- logrel1.v
|   |   |   +-- logrel2.v
|   +-- prelude.v (some stuff that is missing from Iris)
|   +-- program_logic.v
|   +-- lang_generic.v (generic facts about languages with binders and their interpretations)
|   +-- lib/ (derived combinators for gitrees)
|   |   +-- factorial.v
|   |   +-- iter.v
|   |   +-- pairs.v
|   |   +-- sums.v
|   |   +-- while.v
|   |   +-- eq.v (equality for CAS)
|   |   +-- generators.v (generators on top of coroutines)
|   +-- gitree.v (reimport)
|   +-- gitree/ (contains the core definitions related to guarded interaction trees)
|   |   +-- core.v
|   |   +-- greifiers.v (sum of reifiers, parameterized with context-dependency flag)
|   |   +-- lambda.v
|   |   +-- reductions.v (reductions, parameterized with context-dependency flag)
|   |   +-- reify.v (reifiers, parameterized with context-dependency flag)
|   |   +-- subofe.v
|   |   +-- weakestpre.v (program logic, parameterized with context-dependency flag)
|   +-- utils/
|   |   +-- finite_sets.v (finite environment compatibility with the substitution framework)
|   |   +-- clwp.v (context-local weakest precondition)
|   |   +-- wbwp.v (well-bracketed weakest precondition)
```

## Papers glossary

### Modular Denotational Semantics for Effects with Guarded Interaction Trees

The version of the formalization that corresponds to the paper can be found under the [tag `popl24`](https://github.com/logsem/gitrees/releases/tag/popl24).
Below we describe the correspondence per-section.

- **Section 3**
  + Definition of guarded interaction trees, constructors, the
    recursion principle, and the destructors are in `gitree/core.v`
  + Signtures for IO and higher-order store are in `examples/store.v`
    and `input_lang/interp.v`
  + The programming operations are in `gitree/lambda.v` and `lib/while.v`
  + The factorial example is in `lib/factorial.v`, and
    the pairs example is in `lib/pairs.v`
- **Section 4**
  + The definition of context-dependent versions of reifiers and the reify function are in `gitree/reify.v`
  + The reduction relation is in `gitree/reductions.v`
  + The specific reifiers for IO and state are in `examples/store.v`
    and `input_lang/interp.v`
- **Section 5**
  + The syntax for λrec,io is in `input_lang/lang.v`
  + The interpretation and the soundness proof are in `input_lang/interp.v`
- **Section 6**
  + The definition of the weakest precondition and the basic rules are
    in `gitree/weakestpre.v`
  + The additional weakest precondition rules are in `program_logic.v`
    and `effects/store.v`
  + The `iter` example is in `lib/iter.v`
- **Section 7**
  + The logical relation and the adequacy proof are in `input_lang/logrel.v`
- **Section 8**
  + The notion of a subeffect is in `gitree/core.v`
  + The notion of a subreifier and the associated definitions are in
    `gitree/greifiers.v`
  + The `fact_io` example is in `examples/factorial.v`
- **Section 9**
  + The syntax for λ⊸,ref is in `affine_lang/lang.v`
  + The logical relations for the type safety of λ⊸,ref and λrec,io
    are in `affine_lang/logrel1.v` and `input_lang/logpred.v`
  + The logical relation for the combined language is in `affine_lang/logrel2.v`

### Context-Dependent Effects in Guarded Interaction Trees
| Paper entry | Coq qualified identifier |
| ----------- | -------------- |
| fig. 10 | ```gitree.reify.sReifier, gitree.reify.reify``` |
| wp-reify-local-context-dependent | ```gitree.weakestpre.wp_subreify_ctx_dep'``` |
| fig. 11 | ```examples.lang_callcc.interp_*``` |
| lemma 3.1 | ```examples.lang_callcc.interp.interp_ectx_hom``` |
| lemma 3.2 | ```examples.lang_callcc.interp.interp_comp``` |
| lemma 3.3 | ```examples.lang_callcc.interp.interp_*_subst``` |
| lemma 3.4 | ```examples.lang_callcc.interp.soundness``` |
| wp-throw | ```effects.callcc.wp_throw'``` |
| wp-callcc | ```effects.callcc.wp_callcc``` |
| fig. 12 | ```examples.lang_callcc.logrel.logrel_valid``` |
| lemma 3.5 | ```examples.lang_callcc.logrel.adequacy``` |
| lemma 3.6 | ```examples.lang_callcc.logrel.obs_ref_bind``` |
| lemma 3.7 | ```examples.lang_callcc.logrel.fundamental*``` |
| reifier-coercion | ```gitree.reify.sReifier_NotCtxDep_min``` |
| fig. 15 | ```examples.input_lang_callcc.logrel.logrel_valid``` |
| wp-input-ctx-dep | ```examples.input_lang_callcc.interp.wp_input'``` |
| wp-output-ctx-dep | ```examples.input_lang_callcc.interp.wp_output'``` |
| fig. 17 | ```examples.delim_lang.lang.Cred``` |
| fig. 18 | ```effects.delim``` |
| fig. 19 | ```examples.delim_lang.interp.interp_*``` |
| theorem 4.1 | ```examples.delim_lang.interp.soundness``` |
| theorem 4.2 | ```examples.delim_lang.logrel.adequacy``` |
| lemma 4.3 | ```examples.delim_lang.logrel.fundamental_*``` |
| lemma 4.4 | ```examples.delim_lang.logrel.compat_HOM_id``` |
| lemma 4.5 | used ad-hoc in ```examples.delim_lang.logrel``` |
| unary logical relation for delim lang | ```examples.delim_lang.logpred``` |
| denotational semantics of embed lang | ```examples.delim_lang.glue.interp_expr``` |
| lemma 5.1 | ```examples.delim_lang.glue.fl``` |
| lemma 5.2 | ```examples.delim_lang.glue.safety``` |

## Notes

### Disjunction property
Some results in the formalization make use of the disjunction property
of Iris: if (P ∨ Q) is provable, then either P or Q are provable on
their own. This propery is used to show safety of the weakest
precondition, and it is related to the difference between internal and
external reductions.

The internal reductions of GITrees is the relation `istep`, as defined
in the paper, and it has type `iProp` as it is an internal relatin.
There is also a similar *external* reduction relation `sstep` which
lives in Coq's `Prop`. We use the `istep` relation in our definitions
(since it is an internal relation), but we want to state the safety
result w.r.t. the external relation `sstep`, which we take to be the
'proper definition' of the reductions for GITrees.

Showing that `internal_step`-safety implies `external_step`-safety
(i.e. that if a GITree can do an `internal_step` then it can also do a
`external_step`) requires the disjunction propety. The disjunction
property for Iris can be shown assuming classical axioms (e.g. LEM) on
the `Prop`-level.

In order not to introduce classical axioms into the whole
formalization, we added the disjunction propety as an assumption to
the safety theorems (`wp_progress_gen`, `wp_tp_progress_gen`) and all
of its instances (e.g. in logical relations).

### Ground type of errors

One other difference with the paper worth mentioning, is that in the
formalization we "hardcode" the type `Err` of errors, whereas in the
paper we leave it parameterized. That is why in the `affine_lang` case
study we use `OtherError` to represent linearity violations, instead
of `Err(Lin)`.
