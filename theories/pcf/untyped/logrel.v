(** Computational adequacy for the untyped model *)
From Equations Require Import Equations.
From iris.base_logic Require Export base_logic.
From iris.prelude Require Import options.
From iris.si_logic Require Import bi siprop.
From iris.proofmode Require Import classes tactics.
From gitrees Require Import prelude pcf.lang pcf.untyped.model.

(** ** Preliminary: *)
(* register typeclasses for the proofmode *)
Local Instance from_modal_contractive {A B : ofe} (x y : A) (F : A -n> B)
     {PROP : bi} `{!BiInternalEq PROP} :

  Contractive F →
  FromModal (PROP1:=PROP) (PROP2:=PROP) True (modality_instances.modality_laterN 1)
    (▷^1 (x ≡ y) : PROP)%I (F x ≡ F y) (x ≡ y).
Proof.
  intros HF.
  rewrite /FromModal /= => _. by apply f_equivI_contractive.
Qed.

Global Instance from_modal_tick x y      {PROP : bi} `{!BiInternalEq PROP} :
  FromModal (PROP1:=PROP) (PROP2:=PROP) True (modality_instances.modality_laterN 1)
    (▷ (x ≡ y) : PROP)%I (D_tick x ≡ D_tick y) (x ≡ y).
Proof. apply from_modal_contractive. apply _. Qed.

Global Instance into_laterN_tick only_head n n' x y :
  nat_cancel.NatCancel n 1 n' 0 →
  IntoLaterN (PROP:=siPropI) only_head n (D_tick x ≡ D_tick y) (x ≡ y) | 2.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN.
  move=> Hn. rewrite !D_tick_eq.
  rewrite D_thunk_inj'.
  by eapply (class_instances_internal_eq.into_laterN_Next only_head).
Qed.

(** * Logical relation *)

Canonical Structure termO Γ τ := leibnizO (tm Γ τ).

(** Case for the natural nubmers *)
Program Definition logrel_nat_pre {Γ}
        (self : termO Γ tnat -n> D -n> siPropO)
 : termO Γ tnat -n> D -n> siPropO := λne M t,
  ((∃ (n : nat), t ≡ D_nat n ∧ ⌜step_beta_clos M 0 (Num n)⌝)
   ∨ (∃ (β : D) (M' M'' : tm Γ tnat),
         t ≡ D_tick β ∧ ⌜step_beta_clos M 0 M'⌝ ∧ ⌜step_beta M' 1 M''⌝ ∧
         ▷ self M'' β))%I.
Next Obligation.
Opaque later_ap. solve_proper. Qed.
Next Obligation. solve_proper. Qed.

Global Instance logrel_nat_pre_contractive {Γ} :
  Contractive (@logrel_nat_pre Γ).
Proof. solve_contractive. Qed.

Definition logrel_nat {Γ} := fixpoint (@logrel_nat_pre Γ).

Lemma logrel_nat_unfold {Γ} M α :
  logrel_nat M α ≡
   ((∃ (n : nat), α ≡ D_nat n ∧ ⌜step_beta_clos M 0 (Num n)⌝)
     ∨ (∃ (β : D) (M' M'' : tm Γ tnat),
         α ≡ D_tick β ∧ ⌜step_beta_clos M 0 M'⌝ ∧ ⌜step_beta M' 1 M''⌝ ∧
         ▷ logrel_nat M'' β))%I.
Proof.
  unfold logrel_nat.
  apply (fixpoint_unfold logrel_nat_pre M _).
Qed.

Global Instance logrel_nat_proper {Γ} :
  Proper ((≡) ==> (≡)) ((@logrel_nat Γ)).
Proof. solve_proper. Qed.

Global Instance logrel_nat_ne {Γ} n :
  Proper ((dist n) ==> ((dist n))) ((@logrel_nat Γ)).
Proof. solve_proper. Qed.


(** Definition by recursion on the type *)
Fixpoint logrel {Γ} (τ : ty) : tm Γ τ → D → siProp :=
  match τ with
  | tnat => λ M x, logrel_nat M x
  | tarr τ1 τ2 => λ M α, ∀ (N : tm Γ τ1) (β : D),
        ▷ logrel τ1 N β → logrel τ2 (M · N) (APP α β)
  end%I.


#[export] Instance logrel_proper {Γ} τ :
  Proper ((≡) ==> (≡) ==> (≡)) (@logrel Γ τ).
Proof. induction τ; simpl; solve_proper. Qed.
#[export] Instance logrel_ne {Γ} τ n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (@logrel Γ τ).
Proof. induction τ; simpl; solve_proper. Qed.

(** ** Additional rules for the logical relation.
Kind of "symbolic execution" rules.
*)
Program Definition logrel_step_0 Γ (τ : ty) (M N : tm Γ τ) (Hst : step_beta M 0 N) :
  (⊢ ∀ α : D, logrel τ N α → logrel τ M α)%I.
Proof.
  induction τ.
  - simpl. iIntros (α).
    rewrite logrel_nat_unfold.
    iDestruct 1 as "[H | H]".
    + iDestruct "H" as (n) "[Heq H]".
      rewrite logrel_nat_unfold. iLeft.
      iExists n. iFrame. iDestruct "H" as %Hstep.
      iPureIntro. change 0 with (0+0); econstructor; eauto.
    + iDestruct "H" as (β M' M'') "(Heq & %HM & %HM'' & H)".
      rewrite (logrel_nat_unfold M α). iRight.
      iExists β, M', M''. repeat iSplit; eauto.
      iPureIntro. change 0 with (0+0).
      econstructor; eauto.
  - iIntros (α) "HN". simpl.
    iIntros (β M') "HM'".
    iSpecialize ("HN" with "HM'").
    iApply IHτ2; eauto.
    by econstructor.
Qed.

Program Definition logrel_step_1 Γ (τ : ty) (M N : tm Γ τ) (Hst : step_beta M 1 N) :
  (⊢ ∀ α : D, ▷ logrel τ N α → logrel τ M (D_tick α))%I.
Proof.
  induction τ.
  - simpl. iIntros (α).
    iIntros "H".
    rewrite (logrel_nat_unfold M). iRight.
    iExists α, M, N. repeat iSplit; eauto.
    { iPureIntro. econstructor. }
  - iIntros (α) "H". cbn[logrel]. iIntros (P β) "H2".
    iSpecialize ("H" with "[H2]").
    { iNext. iExact "H2". }
    iPoseProof (IHτ2 (M · P) (N · P)) as "Hs".
    { econstructor; eauto. }
    rewrite APP_tick_l.
    iApply ("Hs" with "H").
Qed.

(** * Adequacy *)
Lemma logrel_adequacy (M : tm [] tnat) (n k : nat) :
  (⊢ logrel tnat M (D_tick_n k (D_nat n)))
  → step_beta_clos M k (Num n).
Proof.
  intros Hlog.
  cut (⊢ ▷^k ⌜step_beta_clos M k (Num n)⌝ : siProp)%I.
  { intros HH.
    eapply siProp.pure_soundness.
    by eapply (laterN_soundness _ k). }
  iPoseProof Hlog as "H". clear Hlog.
  iInduction k as [|k] "IH" forall (M).
  - iSimpl in "H". rewrite logrel_nat_unfold.
    iDestruct "H" as "[H | H]".
    + iDestruct "H" as (m) "[Hunit %]".
      rewrite D_nat_inj'. iDestruct "Hunit" as %->.
      iPureIntro; eauto.
    + iDestruct "H" as (β M' M'') "(Hβ & %HM & %HM' & H)".
      by rewrite D_nat_not_thunk.
  - iSimpl in "H". rewrite logrel_nat_unfold.
    iDestruct "H" as "[H | H]".
    + iDestruct "H" as (n0) "[Heq1 %]". iExFalso.
      iExFalso. iAssert (D_nat n0 ≡ D_tick_n (S k) (D_nat n))%I with "[Heq1]" as "H".
      { by iRewrite -"Heq1". }
      by rewrite D_nat_not_thunk.
    + iDestruct "H" as (β M' M'') "(Hβ & %HM & %HM' & H)".
      iNext. iRewrite -"Hβ" in "H".
      iSpecialize ("IH" with "H").
      iNext.
      iDestruct "IH" as %IH. iPureIntro.
      (* need some computations of step_clos *)
      eapply step_beta_clos_trans; eauto.
      change (S k) with (1 + k). econstructor; eauto.
Qed.

(** * Fundamental property *)

(** Compatibility lemmas *)
Lemma interp_Y_app (α : D) :
  interp_Y_ish α  ≡ APP α (interp_Y_ish α).
Proof.
  rewrite {1}/interp_Y_ish.
  etrans.
  { eapply (mmuu_unfold interp_Y_pre). }
  cbn-[interp_Y_ish D_tick get_fun mmuu interp_Y_ish].
  repeat f_equiv. intro f.
  simpl_me. reflexivity.
Qed.

Lemma compat_Y Γ (σ : ty) (M : tm Γ (tarr σ σ)) α :
  ⊢ logrel (tarr σ σ) M α → logrel σ (Y M) (interp_Y_ish α).
Proof.
  iIntros "#HM".
  iLöb as "IH".
  iApply logrel_step_0.
  { econstructor. }
  simpl_me. rewrite {2}(interp_Y_app α).
  by iApply "HM".
Qed.

Lemma compat_app Γ (σ σ' : ty) (M : tm Γ (tarr σ σ')) (N : tm Γ σ) α β :
  ⊢ logrel _ M α → ▷ logrel _ N β → logrel _ (M · N) (APP α β).
Proof.
  iIntros "#HM #HN".
  simpl_me. by iApply "HM".
Qed.

Lemma compat_succ Γ (M : tm Γ tnat) α :
  ⊢ logrel tnat M α → logrel _ (Succ M) (SUCC α).
Proof.
  iLöb as "IH" forall (M α).
  iIntros "#H".
  simpl_me.
  rewrite {1}logrel_nat_unfold. iDestruct "H" as "[H1|H1]".
  + iDestruct "H1" as (n) "[Ht %Hn]".
    iRewrite "Ht". rewrite (logrel_nat_unfold (Succ _)). iLeft.
    iExists (S n). iSplit; last first.
    { iPureIntro. eapply (step_beta_clos_trans _ (Succ (Num n))); eauto.
      - eapply step_beta_close_Succ; eauto.
      - eapply step_beta_clos_once; econstructor. }
    by rewrite /SUCC get_nat_nat.
  + iDestruct "H1" as (β M' M'') "[Ht [%HM [%HM' H1]]]".
    rewrite (logrel_nat_unfold (Succ M)). iRight.
    iExists (SUCC β), (Succ M'), (Succ M'').
    repeat iSplit; eauto.
    * iRewrite "Ht". by rewrite /SUCC get_nat_tick.
    * iPureIntro. eapply step_beta_close_Succ; eauto.
    * iPureIntro. by econstructor.
    * iNext. by iApply "IH".
Qed.


Lemma compat_pred Γ (M : tm Γ tnat) α :
  ⊢ logrel tnat M α → logrel _ (Pred M) (PRED α).
Proof.
  iLöb as "IH" forall (M α).
  iIntros "#H".
  simpl_me.
  rewrite {1}logrel_nat_unfold. iDestruct "H" as "[H1|H1]".
  + iDestruct "H1" as (n) "[Ht %Hn]".
    iRewrite "Ht". rewrite (logrel_nat_unfold (Pred _)). iLeft.
    iExists (pred n). iSplit; last first.
    { iPureIntro. eapply (step_beta_clos_trans _ (Pred (Num n))); eauto.
      - eapply step_beta_close_Pred; eauto.
      - eapply step_beta_clos_once; econstructor. }
    by rewrite /PRED get_nat_nat.
  + iDestruct "H1" as (β M' M'') "[Ht [%HM [%HM' H1]]]".
    rewrite (logrel_nat_unfold (Pred _)). iRight.
    iExists (PRED β), (Pred M'), (Pred M'').
    repeat iSplit; eauto.
    * iRewrite "Ht". by rewrite /PRED get_nat_tick.
    * iPureIntro. eapply step_beta_close_Pred; eauto.
    * iPureIntro. by econstructor.
    * iNext. by iApply "IH".
Qed.

(** * Fundamental property *)

Inductive subs2 : list ty → Type :=
| emp_subs2 : subs2 []
| cons_subs2 {Γ τ} :
    forall (t : tm [] τ) (α : D),
    subs2 Γ →
    subs2 (τ::Γ)
.

Equations subs_of_subs2 {Γ} (ss : subs2 Γ) : subs Γ [] :=
  subs_of_subs2 emp_subs2 _ v => idsub _ v;
  subs_of_subs2 (cons_subs2 t α ss) _ Vz := t;
  subs_of_subs2 (cons_subs2 t α ss) _ (Vs v) := subs_of_subs2 ss _ v.

Lemma subs_of_emp_subs2 : subs_of_subs2 emp_subs2 ≡ idsub.
Proof. intros τ v. dependent elimination v. Qed.

Equations interp_ctx_of_subs2 {Γ} (ss : subs2 Γ) : interp_ctx Γ :=
  interp_ctx_of_subs2 emp_subs2 := ();
  interp_ctx_of_subs2 (cons_subs2 t α ss) := (α, interp_ctx_of_subs2 ss).

Equations list_of_subs2 {Γ} (ss : subs2 Γ) : list ({ τ : ty & (tm [] τ * D)%type}) :=
  list_of_subs2 emp_subs2 := [];
  list_of_subs2 (@cons_subs2 _ τ t α ss) := (existT τ (t, α))::list_of_subs2 ss.

Definition subs2_valid {Γ} (ss : subs2 Γ) : siProp :=
  ([∧ list] s∈(list_of_subs2 ss), logrel (projT1 s) (fst (projT2 s)) (snd (projT2 s)))%I.


Lemma logrel_fundamental Γ τ (t : tm Γ τ) :
  ⊢ ∀ ss : subs2 Γ, subs2_valid ss →
                  logrel τ (subst_tm t (subs_of_subs2 ss))
                           (interp_tm t (interp_ctx_of_subs2 ss)).
Proof.
  induction t.
  - (* Nat const *)
    iIntros (ss) "Hss". simpl.
    rewrite logrel_nat_unfold. iLeft.
    iExists n. simp subst_tm interp_tm. simpl.
    iSplit; eauto. iPureIntro. econstructor.
  - (* Var *)
    iIntros (ss) "Hss".
    simp subst_tm interp_tm.
    iInduction ss as [|] "IH"; dependent elimination v.
    + rewrite /subs2_valid. simp list_of_subs2. simpl.
      iDestruct "Hss" as "[H Hss]".
      simp subs_of_subs2 subst_var.
      simp interp_ctx_of_subs2. simpl.
      simp interp_var. simpl. done.
    + rewrite /subs2_valid. simp list_of_subs2. simpl.
      iDestruct "Hss" as "[H Hss]".
      simp subs_of_subs2 interp_var.
      simp interp_ctx_of_subs2. simpl.
      by iApply "IH".
  - (* Lam *)
    iIntros (ss) "Hss". simpl_me.
    iIntros (N β) "HN".
    simp subst_tm. simp interp_tm.
    unfold APP. simpl_me.
    rewrite get_fun_fun. simpl_me.
    Transparent later_ap.
    unfold later_ap. simpl_me.
    Opaque later_ap.
    iApply logrel_step_1.
    { econstructor. } iNext.
    unfold subst1.
    rewrite -subst_comp_s.
    assert ((β, interp_ctx_of_subs2 ss) ≡
        (interp_ctx_of_subs2 (cons_subs2 N β ss))) as Hsbs1.
    { by simp interp_ctx_of_subs2. }
    rewrite Hsbs1.
    assert ((comp_s (subs_lift (subs_of_subs2 ss)) {|N|})
              ≡ subs_of_subs2 (cons_subs2 N β ss)) as Hsbs2.
    { clear. unfold comp_s. intros ? v.
      dependent elimination v;
        simp subs_of_subs2 subs_lift subst_tm; first done.
      unfold tm_lift.
      rewrite -subst_comp_r_s.
      assert ((comp_r_s (λ (τ : ty) (v0 : var [] τ), Vs v0) {|N|})
                ≡ idsub) as ->.
      { clear. intros ? v. unfold comp_r_s.
        reflexivity. }
      apply subst_tm_id. }
    rewrite (subst_tm_proper _ _ _ t _ _ Hsbs2).
    iApply IHt. rewrite /subs2_valid.
    simp list_of_subs2. simpl; eauto.
  - (* App *)
    iIntros (ss) "#Hss".
    simp subst_tm interp_tm. simpl_me.
    iApply compat_app.
    + by iApply IHt1.
    + by iApply IHt2.
  - (* Succ *)
    iIntros (ss) "#Hss".
    simp subst_tm interp_tm. simpl_me.
    iPoseProof (IHt with "Hss") as "H1".
    iSimpl in "H1".
    iApply (compat_succ with "H1").
  - (* Pred *)
    iIntros (ss) "#Hss". simpl.
    simp subst_tm interp_tm. simpl.
    iPoseProof (IHt with "Hss") as "H1".
    iSimpl in "H1".
    iApply (compat_pred with "H1").
  - (* Y *)
    iIntros (ss) "#Hss".
    simp subst_tm interp_tm. simpl.
    iApply compat_Y.
    by iApply IHt.
Qed.

Theorem interp_adequacy (M : tm [] tnat) (k n : nat) :
  interp_tm M () ≡ D_tick_n k (D_nat n) →
  step_beta_clos M k (Num n).
Proof.
  intros H.
  apply logrel_adequacy.
  rewrite -H.
  iPoseProof (logrel_fundamental [] tnat M) as "H".
  iSpecialize ("H" $! emp_subs2 with "[]").
  { rewrite /subs2_valid. simp list_of_subs2. by simpl. }
  simp subs_of_subs2 interp_ctx_of_subs2.
  assert (subst_tm M (subs_of_subs2 emp_subs2) = subst_tm M idsub) as ->.
  { by rewrite subs_of_emp_subs2. }
  by rewrite subst_tm_id.
Qed.
