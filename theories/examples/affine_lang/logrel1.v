(** Unary (Kripke) logical relation for the affine lang *)
From gitrees Require Export gitree program_logic.
From gitrees.examples.affine_lang Require Import lang.
From gitrees.effects Require Import store.
From gitrees.lib Require Import pairs.
Require Import iris.algebra.gmap.
Require Import stdpp.finite.

Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

Lemma fin_to_set_sum {S1 S2 : Set} `{EqDecision S1} `{EqDecision S2} `{EqDecision (S1 + S2)}
  `{Finite S1} `{Finite S2} `{Finite (S1 + S2)}
  `{Countable S1} `{Countable S2} `{Countable (S1 + S2)}
  : let A1 : gset S1 := (fin_to_set S1) in
    let A2 : gset (S1 + S2) := set_map (inl : S1 → S1 + S2) A1 in
    let B1 : gset S2 := (fin_to_set S2) in
    let B2 : gset (S1 + S2) := set_map (inr : S2 → S1 + S2) B1 in
    let C : gset (S1 + S2) := fin_to_set (S1 + S2) in
    C = A2 ∪ B2.
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

Lemma fin_to_set_empty :
  let A : gset ∅ := fin_to_set ∅ in
  let B : gset ∅ := empty in
  A = B.
Proof.
  apply set_eq; intros [].
Qed.

Section InstSum.
  Global Instance EqDecisionLeft {S1 S2 : Set} {H : EqDecision (S1 + S2)} : EqDecision S1.
  Proof.
    intros x y.
    destruct (decide (inl x = inl y)) as [G | G];
      [left; by inversion G | right; intros C; by subst].
  Qed.

  Global Instance EqDecisionRight {S1 S2 : Set} {H : EqDecision (S1 + S2)} : EqDecision S2.
  Proof.
    intros x y.
    destruct (decide (inr x = inr y)) as [G | G];
      [left; by inversion G | right; intros C; by subst].
  Qed.

  Global Instance FiniteLeft {S1 S2 : Set} `{EqDecision S1}
    `{EqDecision (S1 + S2)} `{Finite (S1 + S2)}
    : Finite S1.
  Proof.
    unshelve econstructor.
    - apply (foldr (λ x acc, match x with
                             | inl x => x :: acc
                             | inr _ => acc
                             end) [] (enum (S1 + S2))).
    - set (l := enum (S1 + S2)).
      assert (NoDup l) as K; first apply NoDup_enum.
      clearbody l.
      induction l as [| a l IH]; first constructor.
      destruct a as [a | a]; simpl.
      + constructor.
        * intros C.
          assert (inl a ∈ l) as C'.
          {
            clear -C.
            induction l as [| b l IH]; first inversion C.
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
      assert (inl x ∈ l) as K; first apply elem_of_enum.
      clearbody l.
      induction l as [| a l IH]; first inversion K.
      destruct a as [a | a]; simpl.
      + rewrite elem_of_cons in K.
        destruct K as [K | K].
        * inversion K; subst.
          apply elem_of_cons; by left.
        * apply elem_of_cons; right; by apply IH.
      + rewrite elem_of_cons in K.
        destruct K as [K | K]; first inversion K.
        by apply IH.
  Qed.

  Global Instance FiniteRight {S1 S2 : Set} `{EqDecision S2}
    `{EqDecision (S1 + S2)} `{H : Finite (S1 + S2)}
    : Finite S2.
  Proof.
    unshelve econstructor.
    - apply (foldr (λ x acc, match x with
                             | inl _ => acc
                             | inr x => x :: acc
                             end) [] (enum (S1 + S2))).
    - set (l := enum (S1 + S2)).
      assert (NoDup l) as K; first apply NoDup_enum.
      clearbody l.
      induction l as [| a l IH]; first constructor.
      destruct a as [a | a]; simpl.
      + apply IH.
        by inversion K.
      + constructor.
        * intros C.
          assert (inr a ∈ l) as C'.
          {
            clear -C.
            induction l as [| b l IH]; first inversion C.
            destruct b as [b | b]; simpl.
            - apply elem_of_cons.
              right.
              rewrite foldr_cons in C.
              apply IH.
              apply C.
            - rewrite foldr_cons in C.
              rewrite elem_of_cons in C.
              destruct C as [-> | C].
              + apply elem_of_cons.
                by left.
              + right.
                apply IH.
                apply C.
          }
          by inversion K.
        * apply IH.
          by inversion K.
    - intros x.
      set (l := enum (S1 + S2)).
      assert (inr x ∈ l) as K; first apply elem_of_enum.
      clearbody l.
      induction l as [| a l IH]; first inversion K.
      destruct a as [a | a]; simpl.
      + rewrite elem_of_cons in K.
        destruct K as [K | K]; first inversion K.
        by apply IH.
      + rewrite elem_of_cons in K.
        destruct K as [K | K].
        * inversion K; subst.
          apply elem_of_cons; by left.
        * apply elem_of_cons; right; by apply IH.
  Qed.

End InstSum.

Section InstInc.
  Context (S : Set).

  Global Instance EqDecisionIncN {HS : EqDecision S} (n : nat) : EqDecision (Init.Nat.iter n inc S).
  Proof using S.
    induction n; simpl.
    - apply _.
    - intros [|x] [|y].
      + by left.
      + by right.
      + by right.
      + destruct (decide (x = y)) as [-> |]; first by left.
        right; by inversion 1.
  Qed.

  Global Instance EqDecisionInc {HS : EqDecision S} : EqDecision (inc S).
  Proof using S.
    assert (inc S = Init.Nat.iter 1 inc S) as ->; first done.
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

End InstInc.

Definition sum_map' {A B C : Set} (f : A → C) (g : B → C) : sum A B → C :=
  λ x, match x with | inl x' => f x' | inr x' => g x' end.

Inductive typed : forall {S : Set}, (S → ty) → expr S → ty → Prop :=
(** functions *)
| typed_Var {S : Set} (Ω : S → ty) (v : S)  :
  typed Ω (Var v) (Ω v)
| typed_Lam {S : Set} (Ω : S → ty) (τ1 τ2 : ty) (e : expr (inc S) ) :
  typed (Ω ▹ τ1) e τ2 →
  typed Ω (Lam e) (tArr τ1 τ2)
| typed_App {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tArr τ1 τ2) →
  typed Ω2 e2 τ1 →
  typed (sum_map' Ω1 Ω2) (App e1 e2) τ2
(** pairs *)
| typed_Pair {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 τ1 →
  typed Ω2 e2 τ2 →
  typed (sum_map' Ω1 Ω2) (EPair e1 e2) (tPair τ1 τ2)
| typed_Destruct {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 τ : ty)
  (e1 : expr S1) (e2 : expr (inc (inc S2))) :
  typed Ω1 e1 (tPair τ1 τ2) →
  typed ((Ω2 ▹ τ2) ▹ τ1) e2 τ →
  typed (sum_map' Ω1 Ω2) (EDestruct e1 e2) τ
(** references *)
| typed_Alloc {S : Set} (Ω : S → ty) τ e :
  typed Ω e τ →
  typed Ω (Alloc e) (tRef τ)
| typed_Replace {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tRef τ1) →
  typed Ω2 e2 τ2 →
  typed (sum_map' Ω1 Ω2) (Replace e1 e2) (tPair τ1 (tRef τ2))
| typed_Dealloc {S : Set} (Ω : S → ty) e τ :
  typed Ω e (tRef τ) →
  typed Ω (Dealloc e) tUnit
(** literals *)
| typed_Nat {S : Set} (Ω : S → ty) n :
  typed Ω (LitNat n) tInt
| typed_Bool {S : Set} (Ω : S → ty) b :
  typed Ω (LitBool b) tBool
| typed_Unit {S : Set} (Ω : S → ty) :
  typed Ω LitUnit tUnit
.

Section logrel.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier input_lang.interp.reify_io rs}.
  Notation F := (gReifiers_ops NotCtxDep rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
  Notation iProp := (iProp Σ).

  (* parameters for the kripke logical relation *)
  Variable s : stuckness.
  Context `{A:ofe}.
  Variable (P : A -n> iProp).
  Local Notation expr_pred := (expr_pred s rs P).

  (* interpreting tys *)
  Program Definition protected (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (WP@{rs} Force (IT_of_V αv) @ s {{ Φ }})%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tbool : ITV -n> iProp := λne αv,
    (αv ≡ RetV 0 ∨ αv ≡ RetV 1)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n : nat, αv ≡ RetV n)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tunit : ITV -n> iProp := λne αv,
    (αv ≡ RetV ())%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tpair (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ β1v β2v, IT_of_V αv ≡ pairITV (IT_of_V β1v) (IT_of_V β2v) ∗
                  Φ1 β1v ∗ Φ2 β2v)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∀ βv, Φ1 βv -∗ expr_pred ((IT_of_V αv) ⊙ (Thunk (IT_of_V βv))) Φ2)%I.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_ref (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ (l : loc), αv ≡ RetV l ∗ ∃ βv, pointsto l (IT_of_V βv) ∗ Φ βv)%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tBool => interp_tbool
    | tUnit => interp_tunit
    | tInt  => interp_tnat
    | tPair τ1 τ2 => interp_tpair (interp_ty τ1) (interp_ty τ2)
    | tArr τ1 τ2 => interp_tarr  (interp_ty τ1) (interp_ty τ2)
    | tRef τ => interp_ref (interp_ty τ)
    end.

  Program Definition ssubst_valid {S : Set} `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) (ss : interp_scope S) : iProp
    := ([∗ set] x ∈ (fin_to_set S),
         (expr_pred (ss x) (protected (interp_ty (Ω x))))%I).

  Definition valid1 {S : Set} `{!EqDecision S} `{!Finite S} (Ω : S → ty)
    (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    ∀ ss, heap_ctx
          -∗ (ssubst_valid Ω ss)
          -∗ expr_pred (α ss) (interp_ty τ).

  Lemma ssubst_valid_empty (αs : interp_scope ∅) :
    ⊢ ssubst_valid □ αs.
  Proof.
    iStartProof.
    unfold ssubst_valid.
    match goal with
    | |- context G [big_opS ?a ?b ?c] => assert (c = empty) as ->
    end.
    { apply set_eq; intros []. }
    by iApply big_sepS_empty.
  Qed.

  Lemma ssubst_valid_app
    {S1 S2 : Set} `{!EqDecision S1} `{!Finite S1}
    `{!EqDecision S2} `{!Finite S2}
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty)
    (αs : interp_scope (sum S1 S2)) :
    (ssubst_valid (sum_map' Ω1 Ω2) αs) ⊢
    (ssubst_valid Ω1 (interp_scope_split αs).1)
    ∗ (ssubst_valid Ω2 (interp_scope_split αs).2).
  Proof.
    iIntros "H".
    rewrite /ssubst_valid fin_to_set_sum big_sepS_union; first last.
    {
      apply elem_of_disjoint.
      intros [x | x].
      - rewrite !elem_of_list_to_set.
        intros _ H2.
        apply elem_of_list_fmap_2 in H2.
        destruct H2 as [y [H2 H2']]; inversion H2.
      - rewrite !elem_of_list_to_set.
        intros H1 _.
        apply elem_of_list_fmap_2 in H1.
        destruct H1 as [y [H1 H1']]; inversion H1.
    }
    iDestruct "H" as "(H1 & H2)".
    iSplitL "H1".
    - rewrite big_opS_list_to_set; first last.
      {
        apply NoDup_fmap.
        - intros ??; by inversion 1.
        - apply NoDup_elements.
      }
      rewrite big_sepL_fmap /=.
      rewrite big_sepS_elements.
      iFrame "H1".
    - rewrite big_opS_list_to_set; first last.
      {
        apply NoDup_fmap.
        - intros ??; by inversion 1.
        - apply NoDup_elements.
      }
      rewrite big_sepL_fmap /=.
      rewrite big_sepS_elements.
      iFrame "H2".
  Qed.

  Lemma ssubst_valid_cons {S : Set} `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) (αs : interp_scope S) τ t :
    ssubst_valid Ω αs ∗ expr_pred t (protected (interp_ty τ)) ⊢ ssubst_valid (Ω ▹ τ) (extend_scope αs t).
  Proof.
    iIntros "(H & G)".
    rewrite /ssubst_valid.
    pose (Y := let A := {[VZ]} : @gset (leibnizO (inc S)) _ finite_countable in
               let B := fin_to_set (leibnizO S) : gset (leibnizO S) in
               let C := set_map (VS : S → inc S) B
                   : gset (inc S) in A ∪ C).
    assert (fin_to_set (inc S) = Y) as ->.
    {
      subst Y; simpl.
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
    }
    subst Y; simpl.
    rewrite big_sepS_union; first last.
    {
      apply elem_of_disjoint.
      intros [| x].
      - rewrite !elem_of_list_to_set.
        intros _ H2.
        apply elem_of_list_fmap_2 in H2.
        destruct H2 as [y [H2 H2']]; inversion H2.
      - rewrite !elem_of_list_to_set.
        intros H1 _.
        apply elem_of_singleton_1 in H1.
        inversion H1.
    }
    iSplitL "G".
    - rewrite big_opS_singleton.
      iFrame "G".
    - erewrite big_opS_set_map.
      + iFrame "H".
      + intros ?? H; by inversion H.
  Qed.

  Lemma ssubst_valid_lookup {S : Set} `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) (αs : interp_scope S) x :
    ssubst_valid Ω αs ⊢ expr_pred (αs x) (protected (interp_ty (Ω x))).
  Proof.
    iIntros "H".
    iDestruct (big_sepS_elem_of_acc _ _ x with "H") as "($ & _)";
      first apply elem_of_fin_to_set.
  Qed.

  Lemma compat_pair {S1 S2 : Set}
    `{!EqDecision S1} `{!Finite S1}
    `{!EqDecision S2} `{!Finite S2}
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty) α β τ1 τ2 :
    ⊢ valid1 Ω1 α τ1 -∗
      valid1 Ω2 β τ2 -∗
      valid1 (sum_map' Ω1 Ω2) (interp_pair α β ◎ interp_scope_split) (tPair τ1 τ2).
  Proof.
    Opaque pairITV.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_pair].
    rewrite ssubst_valid_app.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    iApply (expr_pred_bind with "H2").
    iIntros (βv) "Hb". simpl.
    rewrite -> get_val_ITV. simpl.
    iApply (expr_pred_bind with "H1").
    iIntros (αv) "Ha". simpl.
    rewrite -> get_val_ITV. simpl.
    iApply expr_pred_ret.
    simpl.
    iExists _,_.
    by iFrame.
  Qed.

  Lemma compat_destruct {S1 S2 : Set}
    `{!EqDecision S1} `{!Finite S1}
    `{!EqDecision S2} `{!Finite S2}
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty)
    α β τ1 τ2 τ :
    ⊢ valid1 Ω1 α (tPair τ1 τ2)
      -∗ valid1 (Ω2 ▹ τ2 ▹ τ1) β τ
      -∗ valid1 (sum_map' Ω1 Ω2) (interp_destruct α β ◎ interp_scope_split) τ.
  Proof.
    Opaque pairITV thunked thunkedV projIT1 projIT2.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_destruct].
    rewrite ssubst_valid_app.
    iDestruct "Has" as "[Ha1 Ha2]".
    iSpecialize ("H1"  with "Hctx Ha1").
    iApply (expr_pred_bind (LETCTX _) with "H1").
    iIntros (αv) "Ha". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iDestruct "Ha" as (β1 β2) "[#Ha [Hb1 Hb2]]".
    iIntros (x) "Hx".
    iApply wp_let.
    iApply (wp_Thunk with "Hctx").
    {
      repeat intro; simpl.
      repeat f_equiv.
      intro; simpl.
      f_equiv.
      intro B; simpl.
      destruct B as [| [|]]; [by f_equiv | reflexivity | reflexivity].
    }
    iNext. iIntros (l1) "Hl1". simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    {
      repeat intro; simpl.
      repeat f_equiv.
      intro B; simpl.
      destruct B as [| [|]]; [reflexivity | by f_equiv | reflexivity].
    }
    iNext. iIntros (l2) "Hl2". simpl.
    pose (ss' := (extend_scope
                    (extend_scope
                       (interp_scope_split αs).2
                       (IT_of_V (thunkedV (projIT2 (IT_of_V αv)) l2)))
                    (IT_of_V (thunkedV (projIT1 (IT_of_V αv)) l1)))).
    iSpecialize ("H2" $! ss'
                  with "Hctx [-Hx] Hx").
    {
      iApply ssubst_valid_cons.
      iSplitR "Hl1 Hb1".
      - iApply ssubst_valid_cons.
        iSplitL "Ha2"; first done.
        Transparent thunkedV thunked.
        simpl.
        iIntros (z) "Hz".
        simpl.
        iApply wp_val.
        iModIntro.
        iExists z; iFrame.
        iApply wp_lam.
        iNext.
        simpl.
        iApply (wp_bind _ (IFSCtx _ _)).
        iApply (wp_read with "Hctx Hl2").
        iNext. iNext. iIntros "Hl2".
        iApply wp_val. iModIntro.
        unfold IFSCtx. simpl.
        rewrite IF_False; last lia.
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write with "Hctx Hl2").
        iNext. iNext. iIntros "Hl2".
        iRewrite "Ha".
        simpl.
        rewrite projIT2_pairV.
        do 3 (iApply wp_tick; iNext).
        iApply wp_val. iModIntro.
        iApply "Hb2".
      - Transparent thunkedV thunked.
        simpl.
        iIntros (z) "Hz".
        simpl.
        iApply wp_val.
        iModIntro.
        iExists z; iFrame.
        iApply wp_lam.
        iNext.
        simpl.
        iApply (wp_bind _ (IFSCtx _ _)).
        iApply (wp_read with "Hctx Hl1").
        iNext. iNext. iIntros "Hl1".
        iApply wp_val. iModIntro.
        unfold IFSCtx. simpl.
        rewrite IF_False; last lia.
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write with "Hctx Hl1").
        iNext. iNext. iIntros "Hl1".
        iRewrite "Ha".
        simpl.
        rewrite projIT1_pairV.
        do 3 (iApply wp_tick; iNext).
        iApply wp_val. iModIntro.
        iApply "Hb1".
    }
    iApply "H2".
  Qed.

  Lemma compat_alloc {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) α τ:
    ⊢ valid1 Ω α τ -∗
      valid1 Ω (interp_alloc α) (tRef τ).
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iSpecialize ("H" with "Hctx Has").
    simpl. iApply (expr_pred_bind (LETCTX _) with "H").
    iIntros (αv) "Hav". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iApply expr_pred_frame.
    iApply (wp_alloc with "Hctx").
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro. simpl.
    iExists l.
    iSplit; first done.
    iExists αv.
    iFrame "Hl".
    iFrame.
  Qed.

  Lemma compat_replace {S1 S2 : Set}
    `{!EqDecision S1} `{!Finite S1}
    `{!EqDecision S2} `{!Finite S2}
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty) α β τ τ' :
    ⊢ valid1 Ω1 α (tRef τ) -∗
      valid1 Ω2 β τ' -∗
      valid1 (sum_map' Ω1 Ω2) (interp_replace α β ◎ interp_scope_split) (tPair τ (tRef τ')).
  Proof.
    Opaque pairITV.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_replace].
    rewrite ssubst_valid_app.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    iApply (expr_pred_bind (LETCTX _) with "H2").
    iIntros (βv) "Hb". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iApply (expr_pred_bind with "H1").
    iIntros (αv) "Ha". simpl.
    iDestruct "Ha" as (l) "[Ha Ha']".
    iDestruct "Ha'" as (γ) "[Hl Hg]".
    iApply expr_pred_frame.
    iRewrite "Ha". simpl.
    rewrite IT_of_V_Ret.
    rewrite -> get_ret_ret; simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_read with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    simpl. iApply wp_seq.
    { solve_proper. }
    iApply (wp_write with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    rewrite get_val_ITV. simpl.
    rewrite get_val_ITV. simpl.
    iApply wp_val. iModIntro.
    iExists γ, (RetV l).
    iSplit; first done.
    iFrame. eauto with iFrame.
  Qed.

  Lemma compat_dealloc {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) α τ:
    ⊢ valid1 Ω α (tRef τ) -∗
      valid1 Ω (interp_dealloc α) tUnit.
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iSpecialize ("H" with "Hctx Has").
    iApply (expr_pred_bind with "H").
    iIntros (αv) "Ha /=".
    iDestruct "Ha" as (l) "[Ha Ha']".
    iDestruct "Ha'" as (βv) "[Hl Hb]".
    iRewrite "Ha". iApply expr_pred_frame. simpl.
    rewrite IT_of_V_Ret. rewrite -> get_ret_ret. simpl.
    iApply (wp_dealloc with "Hctx Hl").
    iNext. iNext. eauto with iFrame.
  Qed.

  Lemma compat_bool {S : Set}
    `{!EqDecision S} `{!Finite S}
    b (Ω : S → ty) :
    ⊢ valid1 Ω (interp_litbool b) tBool.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret.
    destruct b; simpl; eauto.
  Qed.

  Lemma compat_nat {S : Set}
    `{!EqDecision S} `{!Finite S}
    n (Ω : S → ty) :
    ⊢ valid1 Ω (interp_litnat n) tInt.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret. eauto with iFrame.
  Qed.

  Lemma compat_unit {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) :
    ⊢ valid1 Ω interp_litunit tUnit.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret. eauto with iFrame.
  Qed.

  Lemma compat_var {S : Set}
    `{!EqDecision S} `{!Finite S}
    Ω (v : S) :
    ⊢ valid1 Ω (Force ◎ interp_var v) (Ω v).
  Proof.
    iIntros (ss) "#Hctx Has".
    iIntros (x) "Hx".
    unfold Force.
    simpl.
    iApply (wp_bind rs (AppRSCtx (ss v))).
    { solve_proper. }
    iApply wp_val.
    iModIntro.
    unfold AppRSCtx.
    iApply (wp_bind rs (AppLSCtx (IT_of_V (RetV 0)))).
    { solve_proper. }
    unfold AppLSCtx.
    simpl.
    unfold ssubst_valid.
    iDestruct (ssubst_valid_lookup _ _ v with "Has Hx") as "Has".
    iApply (wp_wand with "Has").
    iIntros (w) "(%y & Hw1 & Hw2)"; simpl.
    iModIntro.
    rewrite IT_of_V_Ret.
    iApply (wp_wand with "Hw1 [Hw2]").
    iIntros (z) "Hz".
    iModIntro.
    iExists y.
    iFrame.
  Qed.

  Lemma compat_app {S1 S2 : Set}
    `{!EqDecision S1} `{!Finite S1}
    `{!EqDecision S2} `{!Finite S2}
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty)
    α β τ1 τ2 :
    ⊢ valid1 Ω1 α (tArr τ1 τ2) -∗
      valid1 Ω2 β τ1 -∗
      valid1 (sum_map' Ω1 Ω2) (interp_app α β ◎ interp_scope_split) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    iEval(cbn-[interp_app]).
    rewrite ssubst_valid_app.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    Local Opaque Thunk.
    iSimpl.
    iApply (expr_pred_bind (LETCTX _) with "H2").
    iIntros (βv) "H2". unfold LETCTX. iSimpl.
    rewrite LET_Val/=.
    iApply (expr_pred_bind (LETCTX _) with "H1").
    iIntros (αv) "H1". unfold LETCTX. iSimpl.
    rewrite LET_Val/=.
    by iApply "H1".
  Qed.

  Lemma compat_lam {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) τ1 τ2 α :
    ⊢ valid1 (Ω ▹ τ1) α τ2 -∗
      valid1 Ω (interp_lam α) (tArr τ1 τ2).
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iIntros (x) "Hx".
    iApply wp_val.
    iModIntro. simpl.
    iExists _; iFrame.
    iIntros (βv) "Hb". clear x.
    iIntros (x) "Hx".
    iApply (wp_bind _ (AppRSCtx _)).
    Local Transparent Thunk.
    Local Opaque thunked thunkedV.
    iSimpl. iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    unfold AppRSCtx.
    iApply wp_lam. iNext.
    iEval(cbn-[thunked]).
    pose (ss' := extend_scope αs (IT_of_V (thunkedV (IT_of_V βv) l))).
    iSpecialize ("H" $! ss'
             with "Hctx [-Hx] Hx").
    {
      iApply ssubst_valid_cons.
      iFrame "Has".
      Local Transparent thunked thunkedV.
      simpl.
      iIntros (x') "Hx".
      iApply wp_val.
      iModIntro.
      iExists x'.
      iFrame "Hx".
      iApply wp_lam.
      iNext.
      iApply (wp_bind _ (IFSCtx _ _)).
      iApply (wp_read with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val. iModIntro.
      unfold IFSCtx. simpl.
      rewrite IF_False; last lia.
      iApply wp_seq.
      { solve_proper. }
      iApply (wp_write with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val. iModIntro.
      iApply "Hb".
    }
    iApply "H".
  Qed.

  Lemma fundamental_affine (S : Set)
    {HE : EqDecision S} {HF : Finite S}
    (Ω : S → ty)
    (e : expr S) τ :
    typed Ω e τ →
    ⊢ valid1 Ω (interp_expr _ e) τ.
  Proof.
    intros H.
    induction H.
    - by iApply compat_var.
    - iApply compat_lam;
        iApply IHtyped.
    - iApply (@compat_app S1 S2 EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
      + iApply IHtyped1.
      + iApply IHtyped2.
    - iApply (@compat_pair S1 S2 EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
      + iApply IHtyped1.
      + iApply IHtyped2.
    - iApply (@compat_destruct S1 S2 EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
      + iApply IHtyped1.
      + iApply IHtyped2.
    - iApply compat_alloc;
        iApply IHtyped.
    - iApply (@compat_replace S1 S2 EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
      + iApply IHtyped1.
      + iApply IHtyped2.
    - iApply compat_dealloc;
        iApply IHtyped.
    - by iApply compat_nat.
    - by iApply compat_bool.
    - by iApply compat_unit.
  Qed.

End logrel.

Arguments interp_tarr {_ _ _ _ _ _ _ _ _ _ _ _ _} Φ1 Φ2.
Arguments interp_tbool {_ _ _ _ _ _}.
Arguments interp_tnat {_ _ _ _ _ _}.
Arguments interp_tunit {_ _ _ _ _ _}.
Arguments interp_ty {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} τ.

Local Definition rs : gReifiers NotCtxDep 2 :=
  gReifiers_cons NotCtxDep reify_store (gReifiers_cons NotCtxDep input_lang.interp.reify_io (gReifiers_nil NotCtxDep)).

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Require Import gitrees.gitree.greifiers.

Program Definition ı_scope R `{!Cofe R} : @interp_scope (gReifiers_ops NotCtxDep rs) R _ Empty_set := λne (x : ∅), match x with end.

Lemma logrel1_adequacy cr Σ R `{!Cofe R, !SubOfe natO R, !SubOfe unitO R, !SubOfe locO R} `{!invGpreS Σ}
  `{!statePreG rs R Σ} `{!heapPreG rs R Σ} τ
  (α : interp_scope ∅ -n>  IT (gReifiers_ops NotCtxDep rs) R) (β : IT (gReifiers_ops NotCtxDep rs) R) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ},
      (£ cr ⊢ valid1 rs notStuck (λne _: unitO, True)%I □ α τ)%I) →
  ssteps (gReifiers_sReifier NotCtxDep rs) (α (ı_scope _)) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier NotCtxDep rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier NotCtxDep rs) β st' β1 st1)
      ∨ (∃ e, β ≡ Err e ∧ notStuck e)).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety (S cr)); eauto.
  { apply Hdisj. }
  { by rewrite Hb. }
  intros H1 H2.
  exists (λ _, True)%I. split.
  { apply _. }
  iIntros "[[Hone Hcr] Hst]".
  pose (σ := st.1).
  pose (ios := st.2.1).
  iMod (new_heapG rs σ) as (H3) "H".
  iAssert (has_substate σ ∗ has_substate ios)%I with "[Hst]" as "[Hs Hio]".
  { unfold has_substate, has_full_state.
    assert (of_state NotCtxDep rs (IT (gReifiers_ops NotCtxDep rs) _) st ≡
            of_idx NotCtxDep rs (IT (gReifiers_ops NotCtxDep rs) _) sR_idx (sR_state σ)
            ⋅ of_idx NotCtxDep rs (IT (gReifiers_ops NotCtxDep rs) _) sR_idx (sR_state ios)) as ->; last first.
    { rewrite -own_op. done. }
    unfold sR_idx. simpl.
    intro j.
    rewrite discrete_fun_lookup_op.
    inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 0%fin)). done. }
    intros j. inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 1%fin)). done. }
    intros i. inversion i. }
  iApply fupd_wp.
  iMod (inv_alloc (nroot.@"storeE") _ (∃ σ, £ 1 ∗ has_substate σ ∗ own (heapG_name rs) (●V σ))%I with "[-Hcr]") as "#Hinv".
  { iNext. iExists _. iFrame. }
  simpl.
  iPoseProof (@Hlog _ _ _ with "Hcr") as "Hlog".
  iSpecialize ("Hlog" $! (ı_scope _) with "Hinv []").
  { iApply ssubst_valid_empty. }
  iSpecialize ("Hlog" $! tt with "[//]").
  iModIntro.
  iApply (wp_wand with "Hlog").
  eauto with iFrame.
Qed.

Definition R := sumO locO (sumO unitO natO).

Lemma logrel1_safety e τ (β : IT (gReifiers_ops NotCtxDep rs) R) st st' k :
  typed □ e τ →
  ssteps (gReifiers_sReifier NotCtxDep rs) (interp_expr rs e (ı_scope _)) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier NotCtxDep rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs R;heapΣ rs R]).
  eapply (logrel1_adequacy 0 Σ); eauto; try apply _.
  iIntros (? ? ?) "_".
  iApply (fundamental_affine rs notStuck (λne _ : unitO, True)%I).
  apply Hty.
Qed.
