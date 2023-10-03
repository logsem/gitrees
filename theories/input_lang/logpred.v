(** Unary (Kripke) logical relation for the IO lang *)
From Equations Require Import Equations.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang Require Import lang interp.

Section io_lang.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F natO).
  Notation ITV := (ITV F natO).
  Context `{!invGS Σ, !stateG rs Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).

  Variable s : stuckness.
  Context {A:ofe}.
  Variable (P : A → iProp).
  Context `{!NonExpansive P}.

  Local Notation tyctx := (tyctx ty).
  Local Notation expr_pred := (expr_pred s rs P).

  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n, αv ≡ RetV n)%I.
  Solve All Obligations with solve_proper.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) := λne αv,
    (□ ∀ σ βv, has_substate σ -∗
               Φ1 βv -∗
               expr_pred (IT_of_V αv ⊙ (IT_of_V βv)) (λne v, ∃ σ', Φ2 v ∗ has_substate σ'))%I.
  Solve All Obligations with solve_proper.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tnat => interp_tnat
    | Tarr τ1 τ2 => interp_tarr (interp_ty τ1) (interp_ty τ2)
    end.

  Definition ssubst_valid {S} (Γ : tyctx S) ss := ssubst_valid rs interp_ty Γ ss.

  #[global] Instance io_lang_interp_ty_pers  τ βv : Persistent (io_lang.interp_ty τ βv).
  Proof. induction τ; apply _. Qed.
  #[global] Instance ssubst_valid_pers {S} (Γ : tyctx S) ss : Persistent (ssubst_valid  Γ  ss).
  Proof. apply _. Qed.

  Program Definition valid1 {S}  (Γ : tyctx S) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    (∀ σ ss, has_substate σ -∗ ssubst_valid Γ ss -∗
          expr_pred (α (interp_ssubst ss)) (λne v, ∃ σ', interp_ty τ v ∗ has_substate σ'))%I.
  Solve Obligations with solve_proper.

  Lemma compat_nat {S} n (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_nat rs n) Tnat.
  Proof.
    iIntros (σ αs) "Hs Has".
    simpl. iApply expr_pred_ret. simpl.
    eauto with iFrame.
  Qed.
  Lemma compat_var {S} Ω τ (v : var S) :
    typed_var Ω v τ →
    ⊢ valid1 Ω (interp_var v) τ.
  Proof.
    intros Hv.
    iIntros (σ ss) "Hs Has". simpl.
    unfold ssubst_valid.
    iInduction Hv as [|? ? ? Ω v] "IH" forall (ss); simpl.
    - dependent elimination ss as [cons_ssubst αv ss].
      rewrite ssubst_valid_cons.
      simp interp_var. simpl.
      iDestruct "Has" as "[H _]".
      iApply expr_pred_ret; simpl; eauto with iFrame.
    - dependent elimination ss as [cons_ssubst αv ss].
      rewrite ssubst_valid_cons.
      simp interp_var. simpl.
      iDestruct "Has" as "[_ H]".
      by iApply ("IH" with "Hs H").
  Qed.
  Lemma compat_if {S} (Γ : tyctx S) τ α β1 β2 :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β1 τ -∗
      valid1 Γ β2 τ -∗
      valid1 Γ (interp_if rs α β1 β2) τ.
  Proof.
    iIntros "H0 H1 H2".
    iIntros (σ ss) "Hs #Has".
    iSpecialize ("H0" with "Hs Has").
    simpl. iApply (expr_pred_bind (IFSCtx _ _) with "H0").
    iIntros (αv) "Ha/=".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Hn".
    unfold IFSCtx. iIntros (x) "Hx".
    iRewrite "Hn".
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply ("H2" with "Hs Has Hx").
    - rewrite IF_True; last lia.
      iApply ("H1" with "Hs Has Hx").
  Qed.
  Lemma compat_input {S} (Γ : tyctx S) :
    ⊢ valid1 Γ (interp_input rs) Tnat.
  Proof.
    iIntros (σ ss) "Hs #Has".
    iApply expr_pred_frame.
    destruct (update_input σ) as [n σ'] eqn:Hinp.
    iApply (wp_input with "Hs") .
    { eauto. }
    iNext. iIntros "_ Hs".
    iApply wp_val. simpl. eauto with iFrame.
  Qed.
  Lemma compat_output {S} (Γ : tyctx S) α :
    ⊢ valid1 Γ α Tnat → valid1 Γ (interp_output rs α) Tnat.
  Proof.
    iIntros "H".
    iIntros (σ ss) "Hs #Has".
    iSpecialize ("H" with "Hs Has").
    simpl.
    iApply (expr_pred_bind (get_ret _) with "H").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Hn".
    iApply expr_pred_frame.
    iRewrite "Hn".
    rewrite get_ret_ret.
    iApply (wp_output with "Hs").
    { reflexivity. }
    iNext. iIntros "_ Hs /=".
    eauto with iFrame.
  Qed.
  Lemma compat_app {S} (Γ : tyctx S) α β τ1 τ2 :
    ⊢ valid1 Γ α (Tarr τ1 τ2) -∗
      valid1 Γ β τ1 -∗
      valid1 Γ (interp_app rs α β) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (σ ss) "Hs #Has". simpl.
    iSpecialize ("H2" with "Hs Has").
    iApply (expr_pred_bind (AppRSCtx _) with "H2").
    iIntros (βv) "Hb/=".
    iDestruct "Hb" as (σ') "[Hb Hs]".
    unfold AppRSCtx.
    iSpecialize ("H1" with "Hs Has").
    iApply (expr_pred_bind (AppLSCtx (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ'') "[Ha Hs]".
    unfold AppLSCtx.
    iApply ("Ha" with "Hs Hb").
  Qed.

  Lemma compat_rec {S} (Γ : tyctx S) τ1 τ2 α :
    ⊢ □ valid1 (consC (Tarr τ1 τ2) (consC τ1 Γ)) α τ2 -∗
      valid1 Γ (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (σ ss) "Hs #Hss".
    pose (env := (interp_ssubst ss)). fold env.
    simp subst_expr.
    pose (f := (ir_unf rs α env)).
    iAssert (interp_rec rs α env ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf". iApply expr_pred_ret. simpl.
    iExists _. iFrame. iModIntro.
    iLöb as "IH". iSimpl.
    clear σ.
    iIntros (σ βv) "Hs #Hw".
    iIntros (x) "Hx".
    iApply wp_lam.
    iNext.
    pose (ss' := cons_ssubst (FunV (Next f)) (cons_ssubst βv ss)).
    iSpecialize ("H" $! _ ss' with "Hs []").
    { unfold ssubst_valid.
      unfold ss'.
      rewrite !ssubst_valid_cons.
      by iFrame "IH Hw Hss". }
    unfold f. simpl.
    unfold ss'. simp interp_ssubst.
    iAssert (IT_of_V (FunV (Next f)) ≡ interp_rec rs α env)%I as "Heq".
    { rewrite interp_rec_unfold. done. }
    iRewrite -"Heq". by iApply "H".
  Qed.

  Lemma compat_natop  {S} (Γ : tyctx S) op α β :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β Tnat -∗
      valid1 Γ (interp_natop _ op α β) Tnat.
  Proof.
    iIntros "H1 H2".
    iIntros (σ ss) "Hs #Has". simpl.
    iSpecialize ("H2" with "Hs Has").
    iApply (expr_pred_bind (NatOpRSCtx _ _) with "H2").
    iIntros (βv) "Hb/=".
    iDestruct "Hb" as (σ') "[Hb Hs]".
    unfold NatOpRSCtx.
    iSpecialize ("H1" with "Hs Has").
    iApply (expr_pred_bind (NatOpLSCtx _ (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ'') "[Ha Hs]".
    unfold NatOpLSCtx.
    iDestruct "Hb" as (n1) "Hb".
    iDestruct "Ha" as (n2) "Ha".
    iRewrite "Hb". iRewrite "Ha".
    simpl. iApply expr_pred_frame.
    rewrite NATOP_Ret. iApply wp_val. simpl.
    eauto with iFrame.
  Qed.

  Lemma fundamental {S} (Γ : tyctx S) e τ :
    typed Γ e τ → ⊢ valid1 Γ (interp_expr rs e) τ
  with fundamental_val {S} (Γ : tyctx S) v τ :
    typed_val Γ v τ → ⊢ valid1 Γ (interp_val rs v) τ.
  Proof.
    - destruct 1.
      + by iApply fundamental_val.
      + by iApply compat_var.
      + iApply compat_rec; iApply fundamental; eauto.
      + iApply compat_app; iApply fundamental; eauto.
      + iApply compat_natop; iApply fundamental; eauto.
      + iApply compat_if;  iApply fundamental; eauto.
      + iApply compat_input.
      + iApply compat_output; iApply fundamental; eauto.
    - destruct 1.
      + iApply compat_nat.
      + iApply compat_rec; iApply fundamental; eauto.
  Qed.
  Lemma fundmanetal_closed (e : expr []) (τ : ty) :
    typed empC e τ →
    ⊢ valid1 empC (interp_expr rs e) τ.
  Proof. apply fundamental. Qed.

End io_lang.

Local Definition rs : gReifiers _ := gReifiers_cons reify_io gReifiers_nil.

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logpred_adequacy cr Σ `{!invGpreS Σ}`{!statePreG rs Σ} τ (α : unitO -n> IT (gReifiers_ops rs) natO) (β : IT (gReifiers_ops rs) natO) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs Σ},
      (£ cr ⊢ valid1 rs notStuck (λ _:unitO, True)%I empC α τ)%I) →
  ssteps (gReifiers_sReifier rs) (α ()) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
      ∨ (∃ e, β ≡ Err e ∧ notStuck e)).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety cr); eauto.
  { apply Hdisj. }
  { by rewrite Hb. }
  intros H1 H2.
  exists (interp_ty _ notStuck (λ _:unitO, True) τ)%I. split.
  { apply _. }
  iIntros "[Hcr  Hst]".
  iPoseProof (Hlog with "Hcr") as "Hlog".
  destruct st as [σ []].
  iAssert (has_substate σ) with "[Hst]" as "Hs".
  { unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) natO) (σ,()) ≡
            of_idx rs (IT (gReifiers_ops rs) natO) sR_idx (sR_state σ)) as ->; last done.
    intro j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    { inv_fin j; first done.
      intros i. inversion i. }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
  }
  iSpecialize ("Hlog" $! σ with "Hs []").
  { iApply ssubst_valid_nil. }
  iSpecialize ("Hlog" $! tt with "[//]").
  iApply (wp_wand with"Hlog").
  iIntros ( βv). simpl. iDestruct 1 as (_) "[H _]".
  iDestruct "H" as (σ1') "[$ Hsts]".
  done.
Qed.

Lemma io_lang_safety e τ σ st' β k :
  typed empC e τ →
  ssteps (gReifiers_sReifier rs) (interp_expr _ e ()) (σ,()) β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Htyped Hsteps.
  pose (Σ:=#[invΣ;stateΣ rs]).
  eapply (logpred_adequacy 0 Σ); eauto.
  intros ? ?. iIntros "_".
  by iApply fundamental.
Qed.
