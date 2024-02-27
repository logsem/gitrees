Require Import Binding.Set Binding.Inc.
Require Import Init.Nat.

(* only fin_S_inv is really needed *)
Require Import stdpp.fin.

Section ResolutionDeBruijn.
  Class Resolver (D : Set) (n : nat) := { resolve : fin n -> D }.

  Global Instance ResolverEmpty : Resolver Empty_set 0.
  Proof.
    constructor.
    apply fin_0_inv.
  Defined.

  Global Instance ResolverInc {D : Set} (n : nat) `{Resolver D n} : Resolver (inc D) (S n).
  Proof.
    constructor.
    apply fin_S_inv.
    - apply VZ.
    - intros x; apply VS, resolve, x.
  Defined.

  Global Instance ResolverIncNEmpty {n : nat} : Resolver (iter n inc Empty_set) n.
  Proof.
    induction n; apply _.
  Defined.

End ResolutionDeBruijn.

Section SetPureResolver.
  Context {F : Set → Type}
    {SPC : SetPureCore F}.

  Definition set_pure_resolver {D} {n} `{Resolver D n} (fn : fin n) : F D := (@set_pure _ _ D (resolve fn)).

End SetPureResolver.
