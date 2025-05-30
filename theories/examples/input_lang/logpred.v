(** Unary (Kripke) logical relation for the IO lang *)
From gitrees Require Import gitree program_logic lang_generic.
From gitrees.examples.input_lang Require Import lang interp.
Require Import Binding.Lib Binding.Set Binding.Env.
Require Import gitrees.gitree.greifiers.

Import IF_nat.

Section io_lang.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).

  Variable s : stuckness.
  Context {A : ofe}.
  Variable (P : A -n> iProp).

  Local Notation expr_pred := (expr_pred s rs P).

  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n : nat, αv ≡ RetV n)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) := λne αv,
      (□ ∀ βv, Φ1 βv
               -∗ expr_pred (IT_of_V αv ⊙ (IT_of_V βv))
                    (λne v, Φ2 v))%I.
  Solve All Obligations with solve_proper.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tnat => interp_tnat
    | Tarr τ1 τ2 => interp_tarr (interp_ty τ1) (interp_ty τ2)
    end.

  Notation ssubst_valid := (ssubst_valid1 rs ty interp_ty expr_pred).

  #[global] Instance io_lang_interp_ty_pers  τ βv : Persistent (io_lang.interp_ty τ βv).
  Proof. induction τ; apply _. Qed.

  Program Definition valid1 {S : Set} (Γ : S → ty) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    (∀ ss, io_ctx rs -∗ ssubst_valid Γ ss
           -∗ expr_pred (α ss) (λne v, interp_ty τ v))%I.
  Solve Obligations with solve_proper.

  Lemma compat_nat {S : Set} n (Ω : S → ty) :
    ⊢ valid1 Ω (interp_nat rs n) Tnat.
  Proof.
    iIntros (αs) "#Hio Has".
    simpl. iApply expr_pred_ret. simpl.
    eauto with iFrame.
  Qed.

  Lemma compat_var {S : Set} (Ω : S → ty) (v : S) :
    ⊢ valid1 Ω (interp_var v) (Ω v).
  Proof.
    iIntros (ss) "#Hio Has". simpl.
    iIntros (x) "HP".
    simpl.
    iSpecialize ("Has" $! v x with "HP").
    iApply (wp_wand with "Has").
    iIntros (v') "HH".
    simpl.
    iDestruct "HH" as "(%y & HH & HP')".
    iModIntro.
    iExists y.
    iFrame "HP'".
    iFrame.
  Qed.

  Lemma compat_if {S : Set} (Γ : S → ty) τ α β1 β2 :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β1 τ -∗
      valid1 Γ β2 τ -∗
      valid1 Γ (interp_if rs α β1 β2) τ.
  Proof.
    iIntros "H0 H1 H2".
    iIntros (ss) "#Hio #Has".
    iSpecialize ("H0" with "Hio Has").
    simpl.
    iApply (expr_pred_bind (IFSCtx _ _) with "H0").
    iIntros (αv) "Ha/=".
    iDestruct "Ha" as (n) "Hn".
    unfold IFSCtx. iIntros (x) "Hx".
    iRewrite "Hn".
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply ("H2" with "Hio Has Hx").
    - rewrite IF_True; last lia.
      iApply ("H1" with "Hio Has Hx").
  Qed.

  Lemma compat_input {S : Set} (Γ : S → ty) :
    ⊢ valid1 Γ (interp_input rs) Tnat.
  Proof.
    iIntros (ss) "#Hio #Has".
    iApply expr_pred_frame.
    iApply (wp_input_agnostic with "Hio").
    iNext. iIntros (?).
    iApply wp_val. simpl. eauto with iFrame.
  Qed.

  Lemma compat_output {S : Set} (Γ : S → ty) α :
    ⊢ valid1 Γ α Tnat → valid1 Γ (interp_output rs α) Tnat.
  Proof.
    iIntros "H".
    iIntros (ss) "#Hio #Has".
    iSpecialize ("H" with "Hio Has").
    simpl.
    iApply (expr_pred_bind (get_ret _) with "H").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (n) "Hn".
    iApply expr_pred_frame.
    iRewrite "Hn".
    rewrite get_ret_ret.
    iApply (wp_output_agnostic with "Hio").
    iNext.
    eauto with iFrame.
  Qed.

  Lemma compat_app {S : Set} (Γ : S → ty) α β τ1 τ2 :
    ⊢ valid1 Γ α (Tarr τ1 τ2) -∗
      valid1 Γ β τ1 -∗
      valid1 Γ (interp_app rs α β) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (ss) "#Hio #Has". simpl.
    iSpecialize ("H2" with "Hio Has").
    iApply (expr_pred_bind (AppRSCtx _) with "H2").
    iIntros (βv) "Hb/=".
    unfold AppRSCtx.
    iSpecialize ("H1" with "Hio Has").
    iApply (expr_pred_bind (AppLSCtx (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    unfold AppLSCtx.
    iApply ("Ha" with "Hb").
  Qed.

  Lemma compat_rec {S : Set} (Γ : S → ty) τ1 τ2 α :
    ⊢ □ valid1 (Γ ▹ (Tarr τ1 τ2) ▹ τ1) α τ2 -∗
      valid1 Γ (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (ss) "#Hio #Hss".
    term_simpl.
    pose (f := (ir_unf rs α ss)).
    iAssert (interp_rec rs α ss ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf". iApply expr_pred_ret. simpl.
    iModIntro.
    iLöb as "IH". iSimpl.
    iIntros (βv) "#Hw".
    iIntros (x) "Hx".
    iApply wp_lam.
    iNext. iIntros "Hcl".
    pose (ss' := (extend_scope (extend_scope ss (interp_rec rs α ss)) (IT_of_V βv))).
    iSpecialize ("H" $! ss' with "Hio []").
    {
      unfold ssubst_valid.
      iIntros ([| [|]]); term_simpl.
      - iModIntro; by iApply expr_pred_ret.
      - iModIntro.
        iRewrite "Hf".
        iIntros (x') "Hx".
        iApply wp_val.
        iModIntro.
        iExists x'.
        iFrame "Hx".
        iModIntro.
        iApply "IH".
      - iApply "Hss".
    }
    unfold f.
    by iApply "H".
  Qed.

  Lemma compat_natop {S : Set} (Γ : S → ty) op α β :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β Tnat -∗
      valid1 Γ (interp_natop _ op α β) Tnat.
  Proof.
    iIntros "H1 H2".
    iIntros (ss) "#Hio #Has". simpl.
    iSpecialize ("H2" with "Hio Has").
    iApply (expr_pred_bind (NatOpRSCtx _ _) with "H2").
    iIntros (βv) "Hb/=".
    unfold NatOpRSCtx.
    iSpecialize ("H1" with "Hio Has").
    iApply (expr_pred_bind (NatOpLSCtx _ (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    unfold NatOpLSCtx.
    iDestruct "Hb" as (n1) "Hb".
    iDestruct "Ha" as (n2) "Ha".
    iRewrite "Hb". iRewrite "Ha".
    simpl. iApply expr_pred_frame.
    rewrite NATOP_Ret. iApply wp_val. simpl.
    eauto with iFrame.
  Qed.

  Lemma fundamental {S : Set} (Γ : S → ty) e τ :
    typed Γ e τ → ⊢ valid1 Γ (interp_expr rs e) τ
  with fundamental_val {S : Set} (Γ : S → ty) v τ :
    typed_val Γ v τ → ⊢ valid1 Γ (interp_val rs v) τ.
  Proof.
    - destruct 1.
      + by iApply fundamental_val.
      + subst. by iApply compat_var.
      + iApply compat_app; iApply fundamental; eauto.
      + iApply compat_natop; iApply fundamental; eauto.
      + iApply compat_if;  iApply fundamental; eauto.
      + iApply compat_input.
      + iApply compat_output; iApply fundamental; eauto.
    - destruct 1.
      + iApply compat_nat.
      + iApply compat_rec; iApply fundamental; eauto.
  Qed.

  Lemma fundmanetal_closed (e : expr ∅) (τ : ty) :
    typed □ e τ →
    ⊢ valid1 □ (interp_expr rs e) τ.
  Proof. apply fundamental. Qed.

End io_lang.

Arguments interp_ty {_ _ _ _ _ _ _ _ _ _} τ.
Arguments interp_tarr {_ _ _ _ _ _ _ _ _} Φ1 Φ2.

Local Definition rs : gReifiers NotCtxDep _ := gReifiers_cons reify_io gReifiers_nil.

#[local] Parameter Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Program Definition InputLangGitreeGS {R} `{!Cofe R}
  {a : is_ctx_dep} {n} (rs : gReifiers a n)
  (Σ : gFunctors)
  (H1 : invGS Σ) (H2 : stateG rs R Σ)
  : gitreeGS_gen rs R Σ :=
  GitreeG rs R Σ H1 H2
    (λ _ σ, @state_interp _ _ rs R _ _ H2 σ)
    (λ _, True%I)
    (λ _, True%I)
    _
    (λ x, x)
    _
    _
    _.
Next Obligation.
  intros; simpl.
  iIntros "?". by iModIntro.
Qed.
Next Obligation.
  intros; simpl. iSplit; iIntros "H".
  - by iFrame "H".
  - by iDestruct "H" as "(_ & ?)".
Qed.

Lemma logpred_adequacy cr Σ R `{!Cofe R, SubOfe natO R}
  `{!invGpreS Σ} `{!statePreG rs R Σ} τ
  (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R)
  (β : IT (gReifiers_ops rs) R) st st' k :
  (∀ `{H1 : !gitreeGS_gen rs R Σ},
      (£ cr ⊢ valid1 rs notStuck (λne _ : unitO, True)%I □ α τ)%I) →
  external_steps (gReifiers_sReifier rs) (α ı_scope) st β st' [] k →
  is_Some (IT_to_V β)
  ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) β st' β1 st1 l)
   ∨ (∃ e : errorO, β ≡ Err e ∧ notStuck e).
Proof.
  intros Hlog Hst.
  eapply (wp_progress_gen Σ 1 NotCtxDep rs (S cr) (λ x, x) notStuck
            [] k (α ı_scope) β st st' Hdisj Hst).
  intros H1 H2.
  pose H3 : gitreeGS_gen rs R Σ := InputLangGitreeGS rs Σ H1 H2.
  simpl in H3.
  exists (interp_ty (s:=notStuck) (P:=(λne _:unitO, True)) τ)%I. split.
  { apply _. }
  iExists (@state_interp_fun _ _ rs _ _ _ H3).
  iExists (@aux_interp_fun _ _ rs _ _ _ H3).
  iExists (@fork_post _ _ rs _ _ _ H3).
  iExists (@fork_post_ne _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_mono _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_ne _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_decomp _ _ rs _ _ _ H3).  
  simpl.
  iAssert (True%I) as "G"; first done; iFrame "G"; iClear "G".
  iModIntro. iIntros "((Hone & Hcr) & Hst)".
  iPoseProof (Hlog H3 with "Hcr") as "Hlog".
  destruct st as [σ []].
  iAssert (has_substate σ) with "[Hst]" as "Hs".
  {
    unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) _) (σ,()) ≡
            of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state σ)) as ->; last done.
    intro j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    {
      inv_fin j; first done.
      intros i. inversion i.
    }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
  }
  iApply fupd_wp.
  iMod (inv_alloc (nroot.@"ioE") _
          (∃ σ,
             £ 1 ∗ has_substate (σ : oFunctor_car
                    (sReifier_state reify_io)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)))%I
         with "[Hone Hs]") as "#Hinv".
  {
    iNext. iExists σ.
    iFrame "Hone Hs".
  }
  iSpecialize ("Hlog" with "Hinv []").
  {
    iIntros (x).
    destruct x.
  }
  iSpecialize ("Hlog" $! tt with "[//]").
  iApply (wp_wand with"Hlog").
  iModIntro.
  iIntros ( βv). simpl. iDestruct 1 as (_) "[H _]".
  by iFrame.
Qed.

Lemma io_lang_safety e τ σ st' (β : IT (sReifier_ops (gReifiers_sReifier rs)) natO) k :
  typed □ e τ →
  external_steps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) (σ, ()) β st' [] k →
  is_Some (IT_to_V β)
  ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) β st' β1 st1 l).
Proof.
  intros Htyped Hsteps.
  cut (is_Some (IT_to_V β)
       ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) β st' β1 st1 l)
       ∨ (∃ e : errorO, β ≡ Err e ∧ notStuck e)).
  {
    intros [H | [H | [? [? H]]]].
    - by left.
    - by right.
    - done.
  }
  pose (Σ:=#[invΣ;stateΣ rs natO]).
  assert (invGpreS Σ).
  { apply _. }
  assert (statePreG rs natO Σ).
  { apply _. }
  eapply (logpred_adequacy 0 Σ); eauto.
  intros ?. iIntros "_".
  by iApply fundamental.
Qed.
