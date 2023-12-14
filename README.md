# Guarded Interaction Trees

This is the Coq formalization of guarded interaction trees, associated examples and case studies.

## Installation instructions

To install the formalization you will need the Iris, std++, and Equations packages.
The dependencies can be easily installed using [Opam](https://opam.ocaml.org/) with the following commands:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install . --deps-only
```

Then the formalization can be compiled with `make` and installed with
`make install`. You can pass the additional parameters to compile the
formalization using multiple cores, e.g. `make -j 3` for compiling
using 3 threads.

## Code Overview

All the code lives in the `theories` folder. Below is the quick guide
to the code structure.

- `gitree/` -- contains the core definitions related to guarded interaction trees
- `input_lang/` -- formalization of the language with io, the soundness and adequacy
- `input_lang_callcc/` -- formalization of the language with io, throw and call/cc, the soundness and adequacy
- `affine_lang/` -- formalization of the affine language, type safety of the language interoperability
- `examples/` -- some other smaller examples
- `lang_generic.v` -- generic facts about languages with binders and their interpretations, shared by `input_lang` and `affine_lang`
- `lang_generic_sem.v` -- generic facts about languages with a different representation of binders and their interpretations, used for `input_lang_callcc`
- `prelude.v` -- some stuff that is missing from Iris

### References from the paper to the code

- **Section 3**
  + Definition of guarded interaction trees, constructors, the
    recursion principle, and the destructors are in `gitree/core.v`
  + Signtures for IO and higher-order store are in `examples/store.v`
    and `input_lang/interp.v`
  + The programming operations are in `gitree/lambda.v` and `examples/while.v`
  + The factorial example is in `examples/factorial.v`, and
    the pairs example is in `examples/pairs.v`
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
    and `examples/store.v`
  + The `iter` example is in `examples/iter.v`
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

## Notes

### Representations of binders 1
For the representation of languages with binders, we follow the
approach of (Benton, Hur, Kennedy, McBride, JAR 2012) with well-scoped
terms and substitutions/renamings. (`input_lang`, `affine_lang`)

### Representations of binders 2
For `input_lang_callcc` we use a binder library, implemented by Filip
Sieczkowski and Piotr Polesiuk.

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

Showing that `istep`-safety implies `sstep`-safety (i.e. that if a
GITree can do an `istep` then it can also do a `sstep`) requires the
disjunction propety. The disjunction property for Iris can be shown
assuming classical axioms (e.g. LEM) on the `Prop`-level.

In order not to introduce classical axioms into the whole
formalization, we added the disjunction propety as an assumption to
the safety theorem (`wp_safety`) and all of its instances (e.g. in
logical relations).

### Ground type of errors

One other difference with the paper worth mentioning, is that in the
formalization we "hardcode" the type `Err` of errors, whereas in the
paper we leave it parameterized. That is why in the `affine_lang` case
study we use `OtherError` to represent linearity violations, instead
of `Err(Lin)`.
