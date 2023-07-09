# Guarded Interaction Trees

This is the Coq formalization of guarded interaction trees, associated examples and case studies.

## Installation instructions

To install the formalization you will need the Iris, std++, and Equations packages.
The dependencies can be easily installed with the following commands:

```
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

- *Section 3* contains material from `gitree/core.v`,
  `gitree/lambda.v`, `examples/store.v`, `examples/factorial.v`, and
  `examples/pairs.v`
- *Section 4* contains material from `gitree/reify.v`,
  `gitree/reductions.v`, and it covers additional parts of
  `examples/store.v` and `input_lang/interp.v`
- *Section 5* contains material from `input_lang/lang.v` and
  `input_lang/interp.v`
- *Section 6* contains material from `gitree/weakestpre.v` and
  `program_logic.v`, as well as additional parts of `examples/store.v`
- *Section 7* contains material from `input_lang/logrel.v`
- *Section 8* contains material from `gitree/greifiers.v`
- *Section 9* contains material from the `affine_lang/` directory, as
  well as `input_lang/logpred.v`; the type safety for `affine_lang`
  standalone is in `logrel1.v`, and the type safety for the combined
  language is in `logrel2.v`


## Notes

For the representation of languages with binders, we follow the
approach of (Benton, Hur, Kennedy, McBride, 2012) with well-scoped
terms and substitutions/renamings. 

[1]: "Strongly Typed Term Representations in Coq", N. Benton, C.-K. Hur, A. Kennedy, C. McBride, 2012
