# Intro

Guarded Interaction Trees (GITrees) are a framework for providing
semantics for higher-order programming languages with complex effects,
such as concurrency, higher-order store, and I/O. One of the goals of
the framework is to provide a direct translation for higher-order
constructions. The intention is to use it as an alternative or
augmentation to providing operational semantics.

In this document, we provide a description of the framework and short
descriptions of two case studies. This document also describes an
extension for concurrency and reasoning rules about atomic operations
in GITrees.

The document assumes familiarity with the Iris framework and
recommends skimming through Sections 1–6 of [Modular Denotational
Semantics for Effects with Guarded Interaction
Trees](https://doi.org/10.1145/3632854).

For a more complete treatment of GITrees, we refer readers to [Modular
Denotational Semantics for Effects with Guarded Interaction
Trees](https://doi.org/10.1145/3632854), and for the treatment of
context-dependent effects, please refer to [Context-Dependent Effects
in Guarded Interaction
Trees](https://doi.org/10.1007/978-3-031-91121-7_12).

## Notations glossary

| Notation | Coq qualified identifier | Description |
| ----------- | -------------- |
| λit x, f x | `Fun (Next (λne x, f x))` | Wrapper for higher-order functions in GITrees |
| f ⊙ x | `gitree.lambda.APP' f x` | Strict application in GITrees |
| F ♯ X | `oFunctor_apply F X` | oFunctor object action |
| | prelude.mmuu `{!Cofe A, !Inhabited A} (f : laterO A -n> A) : A | fixpoint combinator |

## Basics

The key definition important to this document is that of the guarded
interaction trees (`IT`), located in `gitree/core.v`. In some sense,
it has similar reasoning principles to a regular Rocq inductive type
(injective and disjoint constructors), except that all associated
equations are step-indexed, and it has constructors that are not
allowed in Rocq type theory. Since associated equations are
step-indexed, as a rule of thumb, all functions involving guarded
interaction trees should come with Proper/NonExpansive instances for
rewriting.

The definition of guarded interaction trees is provided along with
injectivity of constructors (the family of `*_inj` lemmas),
disjointness of constructors (the family of `*_ne` lemmas), and its
recursor, `IT_rec`, together with its associated equations
(`IT_rec1_*` and `IT_rec2_*` lemmas).

For each effect, we associate a reifier that defines semantics for it.
Reifiers are defined in `gitree/reify.v`, and their product is defined
in `gitree/greifiers.v`.

Given reifiers for the effects present in GITrees, we define two kinds
of reduction semantics in `gitree/reductions.v`: the internal one (in
Iris `PROP`), and the external one (in Rocq `Prop`). Both reduction
semantics also have reflexive-transitive closures and thread-pool
liftings.

## Usage guide

In this subsection, we describe a general recipe for working with
programming languages using GITrees.

To provide semantics for a concrete language, one first needs to
provide all the required components. Generally, these can be encoded
in two ways: by Church encoding, and by effects.

Church encoding is enabled by the presence of `Fun : later (IT -n> IT)
-n> IT`. The advantage of using Church encoding is that it satisfies
many useful equalities. An example of Church encoding is provided in
`lib/pairs.v`.

```coq
Program Definition pairITV : IT -n> IT -n> IT := λne a b,
      λit f, f ⊙ a ⊙ b.

Definition projIT1 : IT -n> IT := λne t, t ⊙ λit a b, a.
```

This encoding satisfies a number of equalities, in particular, the
expected beta-rule for projections from pairs of values. Note that for
rules involving reductions, we need to reason modulo the number of
`Tick`s.

```coq
Lemma projIT1_pairV α β `{!AsVal α, !AsVal β} : projIT1 (pairITV α β) ≡ Tick_n 3 α.
```

In general, Church encoding does not require assumptions about GITrees.

Effects require some preliminary definitions. First, we need to define
state for the effects. The state for an effect is given by an
`oFunctor`, which is instantiated with GITrees later. For example, the
snippet below shows the definition of state for higher-order store.

```coq
Definition stateF : oFunctor := (gmapOF locO (▶ ∙))%OF.
```

Next, we define semantics for the effect by providing a reifier (e.g.,
`state_read` below), which specifies the effect semantics, and a
signature (e.g., `opsInterp`), which specifies the types of inputs and
outputs for the effect.

```coq
Definition state_read X `{!Cofe X} : loc * (stateF ♯ X) → option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '(l,σ), x ← σ !! l; Some (x, σ, []).

...

Program Definition ReadE : opInterp :=  {|
  Ins := locO;
  Outs := (▶ ∙);
|}.

...

Definition storeE : opsInterp := @[ReadE;WriteE;AllocE;DeallocE;AtomicE].
Canonical Structure reify_store : sReifier NotCtxDep.
```

Note that reifiers may also return a list of GITrees for effects that
can add more threads to the thread pool. For example, a reifier for
`fork` is:

```coq
Definition reify_fork' X `{Cofe X} : (laterO X) * stateO → option (unitO * stateO * listO (laterO X))
  := λ '(o, σ), Some ((), σ, [o]).
```

Once all required components are implemented, we can provide semantics
for a language. To do that, we fix a few parameters:

* Reifiers (i.e., kinds of effects used in the program);
* Context dependency of the reifiers (i.e., whether continuations can be passed explicitly);
* The type of base values.

An example:

```coq
(* Number of reifiers *)
Context {sz : nat}.
(* Row parameter for reifiers, including a flag for context-dependent reifiers *)
Variable (rs : gReifiers NotCtxDep sz).
(* Concrete elements in the row of reifiers *)
           (* Higher-order store *)
Context `{!subReifier reify_store rs
           (* Preemptive concurrency *)
        , !subReifier reify_fork rs}.
(* Row parameter for the type of base values *)
Context {R} `{CR : !Cofe R}.
(* Concrete elements of the row of base value types (e.g., primitive HeapLang literals) *)
Context `{so : !SubOfe base_litO R}.
(* Shorthand notation *)
Notation F := (gReifiers_ops rs).
Notation IT := (IT F R).
Notation ITV := (ITV F R).
```

We can now define the interpretation of a language in GITrees. Below,
we show two clauses of the interpretation of HeapLang. The first
interprets recursive functions using a fixpoint combinator:

```coq
Program Definition interp_rec_pre (f x : binder) (body : varsO -n> IT)
    : laterO (varsO -n> IT) -n> varsO -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : varsO -n> IT) (a : IT),
                      body (binder_insert x a (binder_insert f (self env) env))) self.

...

Definition interp_rec f x body : varsO -n> IT := mmuu (interp_rec_pre f x body).
```

The next code snippet interprets the `load` effect. Note that we control the
evaluation order using `get_ret`, which forces evaluation of `a env`
to a primitive location value and passes it to the effect:

```coq
Program Definition interp_load {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, get_ret (λne l, READ l) (a env).
```

## Program Logic

To reason about GITrees, the framework provides a program logic
(mostly defined in `core/weakestpre.v`), based on internal steps. The
definition mostly follows the one in Iris and provides standard
progress/adequacy lemmas. The program logic is parameterized by the
following `GS`, which includes invariant `GS` (with later credits),
GITrees state `GS` (`stateG`), and some auxiliary parameters:

```coq
Class gitreeGS_gen (Σ : gFunctors) :=
    GitreeG {
        gitreeInvGS :: invGS Σ;
        gitreeStateGS :: stateG rs A Σ;
        state_interp_fun : nat → stateO → iProp Σ;
        aux_interp_fun : nat → iProp Σ;
        fork_post : ITV -> iProp Σ;
        num_later_per_step : nat → nat;
		...
      }.
```

The full fragmented state is `has_fullstate s`. However, for
modularity, we split it into `has_substate s` for each element of
`gReifiers`. `has_substate s` represents the fragmented state for a
single `sReifier`.

`core/weakestpre.v` provides a number of rules related to reification,
but the framework aims to provide separate weakest precondition rules
for each effect. For example, to allow reasoning about higher-order
store with points-to predicates, it suffices to provide the following
typeclasses and assume `heap_ctx`, which ties GITrees state with
`gmap_auth`.

```coq
(* GS for general guarded interaction trees, includes invGS and stateGS *)
Context `{!gitreeGS_gen rs R Σ}.
(* Auxiliary GS for higher-order store *)
Context `{!heapG rs R Σ}.
Notation iProp := (iProp Σ).
```

## Concurrency extension

To represent effects related to preemptive concurrency, we extend
GITree steps with a thread pool similar to HeapLang, and allow
reifiers to add new threads to the thread pool.

To reason about atomic state modifications, we provide a generic
`Atomic` effect with the following signature:

```coq
Program Definition AtomicE : opInterp := {|
  Ins := (locO * ▶ (∙ -n> (∙ * ∙)))%OF;
  Outs := (▶ ∙);
|}.
```

This signature states that the effect takes a location `l` and a
function that returns two GITrees: the first is the return `IT`, and
the second is an `IT` that gets written to the location. `CAS`,
`XCHG`, and `FAA` are encoded by providing concrete functions to
`Atomic`.

## Case study: Extending the Affine Language with Concurrency

Effects relevant to this case study are located in `effects/store.v`,
`effects/io_tape.v`, and `fork.v`.

In `examples/affine/`, we provide an extension of the language
interaction example from [Modular Denotational Semantics for Effects
with Guarded Interaction Trees](https://doi.org/10.1145/3632854). The
language includes a fork effect. Concurrency introduces the following
two changes:

* The glue code is changed to an atomic `XCHG` effect, which flips a bit if a variable was used once, and causes future invocations to produce errors.

  ```coq
  Program Definition thunked : IT -n> locO -n> IT := λne e ℓ,
      λit _, IF (XCHG ℓ (Ret 1)) (Err AffineError) e.
  ```

* The I/O runtime can be shared between threads, which makes the program logic rules used for the logical relation less fine-grained.

  ```coq
  Program Definition io_ctx :=
    inv (nroot.@"io")
      (∃ σ, £ 1 ∗ has_substate σ)%I.

  Lemma wp_input_agnostic (k : natO -n> IT) Φ s :
    io_ctx
    -∗ ▷ (∀ n, WP (k n) @ s {{ Φ }})
    -∗ WP (INPUT k) @ s {{ Φ }}.
  ```

## Case study: HeapLang

Effects relevant to this case study are located in `effects/store.v` and `fork.v`.

In `examples/heap_lang/`, we provide an interpretation of HeapLang.
For this, we use a modified version of HeapLang taken from the Iris
repository. Changes include:

* No prophecy variables;
* CAS is allowed only for primitives (int, bool, unit, and loc).

After providing an interpretation, we can use the framework’s rules to
derive program logic rules about the interpretation:

```coq
Lemma interp_wp_fork (n : IT) (Φ : ITV  -d> iPropO Σ) (e : expr) (env : varsO rs) :
    fork_ctx rs
    -∗ ▷ Φ (RetV ())
    -∗ ▷ WP@{rs} (interp_expr e env) {{ fork_post }}
    -∗ WP@{rs} (interp_expr (Fork e) env) {{ Φ }}.

Lemma wp_cas_succ_hom (l : locO) α (w1 w2 : val) Φ (env : varsO rs) :
    heap_ctx rs
    -∗ ▷ pointsto l (interp_val α env)
    -∗ ▷ (compare (interp_val w2 env) (interp_val α env) ≡ Ret true)
    -∗ ▷ ▷ (pointsto l (interp_val w1 env)
            -∗ WP@{rs} ((pairIT (interp_val α env) (Ret true))) {{ Φ }})
    -∗ WP@{rs} (interp_expr (CmpXchg #l w1 w2) env) {{ Φ }}.
```

## Possible contributions

* If you feel that a particularly interesting effect is missing, feel free to contribute.
* Include products and sums of GITrees in the GITree type. Extending HeapLang CAS to sums of primitives.
* Provide a soundness proof for HeapLang.
