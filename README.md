# Guarded Interaction Trees

This is the Coq formalization of guarded interaction trees, associated examples and case studies.

## Installation instructions

To install the formalization you will need the Iris, std++, and Equations packages.
The dependencies can be easily installed using [Opam](https://opam.ocaml.org/) with the following commands:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
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
- `affine_lang/` -- formalization of the affine language, type safety of the language interoperability
- `examples/` -- some other smaller examples 
- `lang_generic.v` -- generic facts about languages with binders and their interpretations, shared by `input_lang` and `affine_lang`
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
  + The definition of reifiers and the reify function are in `gitree/reify.v`
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

For the representation of languages with binders, we follow the
approach of (Benton, Hur, Kennedy, McBride, JAR 2012) with well-scoped
terms and substitutions/renamings. 

