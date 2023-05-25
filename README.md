# denotational semantics with guarded interaction trees

- `gitree/core.v` -- the main definitions for Guarded Interaction Trees, and the recursion principle
- `gitree/reify.v`, `gitree/reductions.v` -- reification of effects and reductions of gITrees
- `gitree/lambda.v` -- programmming language combinators on the gITrees
- `gitree/weakestpre.v` -- program logic on gITrees
- `input_lang/` -- a language with recursion and an INPUT effect; model and adequacy

## other stuff

There are two formalized models of PCF in the repository, in the `pcf`
directory. The `lang.v` file contains the formalization of PCF and its
operational semantics, in the style of (Benton, Hur, Kennedy, McBride,
2012). The `typed/` directory contains the formalization of the
"typed" model, as adapted from a similar model in guarded type theory
given in (Paviotti, Mogelberg, Birkedal, 2015). The `untyped/`
directory contains the formaliztion of the "untyped" model in the
style of Scott model for untyped lambda calculus. For both models we
show adequacy using a logical relation in the logic of step-indexed
propositions.

## Reading / bibliography

Typed representation of PCF terms in Coq:

- [1]: "Strongly Typed Term Representations in Coq", N. Benton, C.-K. Hur, A. Kennedy, C. McBride, 2012
- [2]: "Some Domain Theory and Denotational Semantics in Coq", N. Benton, A. Kennedy, C. Varming, 2009
- [3]: "Ultrametric Domain Theory and Semantics in Coq", C. Varming, L. Birkedal, 2010

Domain theory in guarded recursion:

- [4]: "The Category-Theoretic Solution of Recursive Metric-Space Equations", L. Birkedal, K. Stovring, J. Thamsborg, 2010
  (induction principle for recursive domain equations)
- [5]: "A Model of PCF in Guarded Type Theory", M. Paviotti, R. Møgelberg, L. Birkedal, 2015
- [6]: "Denotational semantics of recursive types in synthetic guarded domain theory", M. Paviotti, R. Møgelberg, 2016
- [7]: "Two Guarded Recursive Powerdomains for Applicative Simulation", R. Møgelberg, A. Vezzosi, 2021

Interaction trees are related stuff:

- [8]: "Interaction Trees: Representing Recursive and Impure Programs in Coq", 
  Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, Steve Zdancewic.
  <https://arxiv.org/abs/1906.00046>.
  DF: the most comprehensive reference. describes itrees, ktrees, weak bisimulation...
- [9]: "Formal reasoning about layered monadic interpreters",
  Irene Yoon, Yannick Zakowski,Steve Zdancewic.
  <https://www.cis.upenn.edu/~euisuny/paper/fralmi.pdf>
  DF: reifying and playing with effects. shows how to build 'interpreters' in layers, and also reason about equivalence
- [10]: "Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq",
  Nicolas Chappe, Paul He, Ludovic Henrio, Yannick Zakowski, Steve Zdancewic.
  <https://arxiv.org/abs/2211.06863>
- [11]: "Formally Verified Animation for RoboChart Using Interaction Trees",
  Kangfeng Ye, Simon Foster & Jim Woodcock ,
  https://link.springer.com/chapter/10.1007/978-3-031-17244-1_24
- [12]:  "Formally Verified Simulations of State-Rich Processes Using Interaction Trees in Isabelle/HOL",
  Foster, Simon ; Hur, Chung-Kil ; Woodcock, Jim.
  <https://drops.dagstuhl.de/opus/volltexte/2021/14397/>
- [13]: "Semantics for Noninterference with Interaction Trees",
  L. Silver, P. He, E. Cecchetti, A. K. Hirsch, and S. Zdancewic
  <https://ethan.umiacs.io/papers/secure-itrees.pdf>

Other stuff: 
- <https://github.com/DeepSpec/InteractionTrees>
  Coq formalisation of itrees

