Require Import Utf8.

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
