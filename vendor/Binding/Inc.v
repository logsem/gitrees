Require Import Utf8.
Require Import Eqdep.
Require Import Eqdep_dec.

Notation "∅" := Empty_set.

Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ {V}.
Arguments VS {V}.

Definition inc_map {A B : Set} (f : A → B) (m : inc A) : inc B :=
  match m with
  | VZ   => VZ
  | VS x => VS (f x)
  end.

Fixpoint nth_inc n {A : Set} : Nat.iter n inc (inc A) :=
  match n with
  | O   => VZ
  | S n => VS (nth_inc n)
  end.

Notation "& n" := (nth_inc n) (at level 5).

Module IncEqDec (T : DecidableSet) <: DecidableSet.
  Definition U := inc T.U.

  Lemma eq_dec : ∀ x y:U, {x = y} + {x <> y}.
  Proof.
    intros [| x] [| y]; [left; reflexivity | right; inversion 1 | right; inversion 1 |].
    destruct (T.eq_dec x y) as [-> | H2]; [left; reflexivity | right].
    inversion 1; subst; contradiction.
  Qed.
End IncEqDec.
