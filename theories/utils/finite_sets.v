From stdpp Require Export finite gmap.
Require Export Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

Lemma fin_to_set_sum {S1 S2 : Set} `{!EqDecision S1} `{!EqDecision S2}
  `{!Finite S1} `{!Finite S2} `{HE : EqDecision (S1 + S2)} `{HF : @Finite (S1 + S2) HE}
  : fin_to_set (S1 + S2)
    = (set_map inl (fin_to_set S1 : gset S1))
        ∪ (set_map inr (fin_to_set S2 : gset S2))
      :> @gset (S1 + S2) HE (@finite_countable _ HE HF).
Proof.
  apply set_eq.
  intros [x|x]; simpl; split; intros _.
  - apply elem_of_union; left.
    apply elem_of_map_2.
    apply elem_of_fin_to_set.
  - apply elem_of_fin_to_set.
  - apply elem_of_union; right.
    apply elem_of_map_2.
    apply elem_of_fin_to_set.
  - apply elem_of_fin_to_set.
Qed.

Lemma fin_to_set_empty `{HE : EqDecision ∅} `{HF : @Finite ∅ HE} :
  fin_to_set ∅ = empty :> @gset ∅ HE (@finite_countable _ HE HF).
Proof.
  apply set_eq; intros [].
Qed.

Lemma fin_to_set_inc {S : Set} `{!EqDecision S} `{!Finite S}
  `{HE : EqDecision (inc S)} `{HF : @Finite (inc S) HE}
  : fin_to_set (inc S) = ({[VZ]} : gset (inc S)) ∪ (set_map VS (fin_to_set S : gset S))
      :> @gset (inc S) HE (@finite_countable _ HE HF).
Proof.
  apply set_eq.
  intros [| x].
  - split.
    + intros _; apply elem_of_union; left.
      by apply elem_of_singleton.
    + intros _; apply elem_of_fin_to_set.
  - split.
    + intros _; apply elem_of_union; right.
      apply elem_of_map_2, elem_of_fin_to_set.
    + intros H.
      apply elem_of_fin_to_set.
Qed.

Section Sum.
  (* Kenny Loggins starts playing in a background *)

  Lemma EqDecisionLeft {S1 S2 : Set} {H : EqDecision (S1 + S2)} : EqDecision S1.
  Proof.
    intros x y.
    destruct (decide (inl x = inl y)) as [G | G];
      [left; by inversion G | right; intros C; by subst].
  Qed.

  Lemma EqDecisionRight {S1 S2 : Set} {H : EqDecision (S1 + S2)} : EqDecision S2.
  Proof.
    intros x y.
    destruct (decide (inr x = inr y)) as [G | G];
      [left; by inversion G | right; intros C; by subst].
  Qed.

  Lemma FiniteLeft {S1 S2 : Set} `{EqDecision S1}
    `{EqDecision (S1 + S2)} `{Finite (S1 + S2)}
    : Finite S1.
  Proof.
    unshelve econstructor.
    - apply (foldr (λ x acc, match x with
                             | inl x => x :: acc
                             | inr _ => acc
                             end) [] (enum (S1 + S2))).
    - set (l := enum (S1 + S2)).
      assert (NoDup l) as K; [apply (NoDup_enum (S1 + S2)) |].
      clearbody l.
      induction l as [| a l IH]; [constructor |].
      destruct a as [a | a]; simpl.
      + constructor.
        * intros C.
          assert (inl a ∈ l) as C'.
          {
            clear -C.
            induction l as [| b l IH]; [inversion C |].
            destruct b as [b | b]; simpl.
            - rewrite foldr_cons in C.
              rewrite elem_of_cons in C.
              destruct C as [-> | C].
              + apply elem_of_cons.
                by left.
              + right.
                apply IH.
                apply C.
            - apply elem_of_cons.
              right.
              rewrite foldr_cons in C.
              apply IH.
              apply C.
          }
          by inversion K.
        * apply IH.
          by inversion K.
      + apply IH.
        by inversion K.
    - intros x.
      set (l := enum (S1 + S2)).
      assert (inl x ∈ l) as K; [apply elem_of_enum |].
      clearbody l.
      induction l as [| a l IH]; [inversion K |].
      destruct a as [a | a]; simpl.
      + rewrite elem_of_cons in K.
        destruct K as [K | K].
        * inversion K; subst.
          apply elem_of_cons; by left.
        * apply elem_of_cons; right; by apply IH.
      + rewrite elem_of_cons in K.
        destruct K as [K | K]; [inversion K |].
        by apply IH.
  Qed.

  Lemma FiniteRight {S1 S2 : Set} `{EqDecision S2}
    `{EqDecision (S1 + S2)} `{H : Finite (S1 + S2)}
    : Finite S2.
  Proof.
    unshelve econstructor.
    - apply (foldr (λ x acc, match x with
                             | inl _ => acc
                             | inr x => x :: acc
                             end) [] (enum (S1 + S2))).
    - set (l := enum (S1 + S2)).
      assert (NoDup l) as K; [apply NoDup_enum |].
      clearbody l.
      induction l as [| a l IH]; [constructor |].
      destruct a as [a | a]; simpl.
      + apply IH.
        by inversion K.
      + constructor.
        * intros C.
          assert (inr a ∈ l) as C'.
          {
            clear -C.
            induction l as [| b l IH]; [inversion C |].
            destruct b as [b | b]; simpl.
            - apply elem_of_cons.
              right.
              rewrite foldr_cons in C.
              apply IH, C.
            - rewrite foldr_cons in C.
              rewrite elem_of_cons in C.
              destruct C as [-> | C].
              + apply elem_of_cons.
                by left.
              + right.
                apply IH, C.
          }
          by inversion K.
        * apply IH.
          by inversion K.
    - intros x.
      set (l := enum (S1 + S2)).
      assert (inr x ∈ l) as K; [apply elem_of_enum |].
      clearbody l.
      induction l as [| a l IH]; [inversion K |].
      destruct a as [a | a]; simpl.
      + rewrite elem_of_cons in K.
        destruct K as [K | K]; [inversion K |].
        by apply IH.
      + rewrite elem_of_cons in K.
        destruct K as [K | K].
        * inversion K; subst.
          apply elem_of_cons; by left.
        * apply elem_of_cons; right; by apply IH.
  Qed.

End Sum.

Section Inc.
  Context (S : Set).

  Global Instance EqDecisionIncN {HS : EqDecision S} (n : nat) : EqDecision (Init.Nat.iter n inc S).
  Proof using S.
    induction n; simpl.
    - apply _.
    - intros [|x] [|y].
      + by left.
      + by right.
      + by right.
      + destruct (decide (x = y)) as [-> |]; [by left |].
        right; by inversion 1.
  Qed.

  Global Instance EqDecisionInc {HS : EqDecision S} : EqDecision (inc S).
  Proof using S.
    assert (inc S = Init.Nat.iter 1 inc S) as ->; [done |].
    by apply EqDecisionIncN.
  Qed.

  Global Instance FiniteIncN {HS : EqDecision S} (HF : Finite S) (n : nat) {HS' : EqDecision (Init.Nat.iter n inc S)} : Finite (Init.Nat.iter n inc S).
  Proof using S.
    induction n.
    - apply (@surjective_finite S HS HF _ _ id).
      apply _.
    - simpl.
      unshelve eapply (@surjective_finite (option (Init.Nat.iter n inc S))); simpl in *.
      + intros [x |].
        * apply (VS x).
        * apply VZ.
      + apply _.
      + intros [| x]; simpl.
        * exists None; reflexivity.
        * exists (Some x); reflexivity.
  Qed.

  Global Instance FiniteInc {HS : EqDecision S} (HF : Finite S) (HE : EqDecision (inc S)) : Finite (inc S).
  Proof using S.
    assert (J : @Finite (Init.Nat.iter 1 inc S) HE).
    { apply FiniteIncN, HF. }
    simpl in J.
    apply J.
  Qed.

End Inc.
