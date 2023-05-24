(* Logical relation for proving computational adequacy *)
From Equations Require Import Equations.
From iris.algebra Require cofe_solver.
From iris.base_logic Require Export base_logic.
From iris.prelude Require Import options.
From iris.si_logic Require Import bi siprop.
From iris.proofmode Require Import tactics.
From gitrees.pcf Require Import typed.model.

(** * Logical relation *)

Canonical Structure termO C τ := leibnizO (tm C τ).

(* XXX: !!!! *)
(* Opaque lift_unit lift_delay. *)

Program Definition logrel_nat_pre {C}
        (self : termO C tnat -n> interp_ty tnat -n> siPropO)
 : termO C tnat -n> interp_ty tnat -n> siPropO := λne M t,
  ((∃ (n : nat), t ≡ lift_unit n ∧ ⌜step_clos M 0 (Num n)⌝)
   ∨ (∃ (β : interp_ty tnat) (M' M'' : tm C tnat),
         t ≡ lift_tick β ∧ ⌜step_clos M 0 M'⌝ ∧ ⌜step M' 1 M''⌝ ∧
         ▷ self M'' β))%I.
Next Obligation.
Opaque later_ap. solve_proper. Qed.
Next Obligation. solve_proper. Qed.


Global Instance logrel_nat_pre_contractive {C} :
  Contractive (@logrel_nat_pre C).
Proof. solve_contractive. Qed.

Definition logrel_nat {C} := fixpoint (@logrel_nat_pre C).

Lemma logrel_nat_unfold {C} M α :
  logrel_nat M α ≡ ((∃ (n : nat), α ≡ lift_unit n ∧ ⌜step_clos M 0 (Num n)⌝)
   ∨ (∃ (β : interp_ty tnat) (M' M'' : tm C tnat),
         α ≡ lift_tick β ∧ ⌜step_clos M 0 M'⌝ ∧ ⌜step M' 1 M''⌝ ∧
         ▷ logrel_nat M'' β))%I.
Proof.
  unfold logrel_nat.
  apply (fixpoint_unfold logrel_nat_pre M _).
Qed.

Global Instance logrel_nat_proper {C} :
  Proper ((≡) ==> (≡)) ((@logrel_nat C)).
Proof. solve_proper. Qed.

Global Instance logrel_nat_ne {C} n :
  Proper ((dist n) ==> ((dist n))) ((@logrel_nat C)).
Proof. solve_proper. Qed.

Fixpoint logrel {C} (τ : ty) : tm C τ → interp_ty τ → siProp :=
  match τ with
  | tnat => λ M x, logrel_nat M x
  | tarr τ1 τ2 => λ M x, ∀ (N : tm C τ1) (α : interp_ty τ1),
        logrel τ1 N α → logrel τ2 (M · N) (x α)
  end%I.


#[export] Instance logrel_proper {C} τ :
  Proper ((≡) ==> (≡) ==> (≡)) (@logrel C τ).
Proof. induction τ; simpl; solve_proper. Qed.
#[export] Instance logrel_ne {C} τ n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (@logrel C τ).
Proof. induction τ; simpl; solve_proper. Qed.


Program Definition logrel_step_0 C (τ : ty) (M N : tm C τ) (Hst : step M 0 N) :
  (⊢ ∀ α : interp_ty τ, logrel τ N α → logrel τ M α)%I.
Proof.
  induction τ.
  - simpl. unfold interp_ty. iIntros (α).
    rewrite logrel_nat_unfold.
    iDestruct 1 as "[H | H]".
    + iDestruct "H" as (n) "[Heq H]".
      rewrite logrel_nat_unfold. iLeft.
      iExists n. iFrame. iDestruct "H" as %Hstep.
      iPureIntro. change 0 with (0+0); econstructor; eauto.
    + iDestruct "H" as (β M' M'') "(Heq & %HM & %HM'' & H)".
      rewrite (logrel_nat_unfold M). iRight.
      iExists β, M', M''. repeat iSplit; eauto.
      iPureIntro. change 0 with (0+0).
      econstructor; eauto.
  - iIntros (α) "HN". simpl.
    iIntros (β M') "HM'".
    iSpecialize ("HN" with "HM'").
    iApply IHτ2; eauto.
    by econstructor.
Qed.

Program Definition logrel_step_1 C (τ : ty) (M N : tm C τ) (Hst : step M 1 N) :
  (⊢ ∀ α : interp_ty τ, ▷ logrel τ N α → logrel τ M (interp_ty_tick α))%I.
Proof.
  induction τ.
  - simpl. unfold interp_ty. iIntros (α).
    iIntros "H".
    rewrite (logrel_nat_unfold M). iRight.
    iExists α, M, N. repeat iSplit; eauto.
    iPureIntro. econstructor.
  - iIntros (α) "H". cbn[logrel]. iIntros (P β) "H2".
    iSpecialize ("H" with "[H2]").
    { iNext. iExact "H2". }
    iPoseProof (IHτ2 (M · P) (N · P)) as "Hs".
    { econstructor; eauto. }
    iApply ("Hs" with "H").
Qed.

(** * Fundamental property *)

Inductive subs2 : list ty → Type :=
| emp_subs2 : subs2 []
| cons_subs2 {Γ τ} :
    forall (t : tm [] τ)
           (α : interp_ty τ),
    subs2 Γ →
    subs2 (τ::Γ)
.

Equations subs_of_subs2 {Γ} (ss : subs2 Γ) : subs Γ [] :=
  subs_of_subs2 (cons_subs2 t α ss) _ Vz := t;
  subs_of_subs2 (cons_subs2 t α ss) _ (Vs v) := subs_of_subs2 ss _ v.

Equations interp_ctx_of_subs2 {Γ} (ss : subs2 Γ) : interp_ctx Γ :=
  interp_ctx_of_subs2 emp_subs2 := ();
  interp_ctx_of_subs2 (cons_subs2 t α ss) := (α, interp_ctx_of_subs2 ss).

Equations list_of_subs2 {Γ} (ss : subs2 Γ) : list ({ τ : ty & (tm [] τ * interp_ty τ)%type}) :=
  list_of_subs2 emp_subs2 := [];
  list_of_subs2 (@cons_subs2 _ τ t α ss) := (existT τ (t, α))::list_of_subs2 ss.

Definition subs2_valid {Γ} (ss : subs2 Γ) : siProp :=
  ([∧ list] s∈(list_of_subs2 ss), logrel (projT1 s) (fst (projT2 s)) (snd (projT2 s)))%I.

Lemma logrel_Y C (σ : ty) (M : tm C (tarr σ σ)) α (E : interp_ctx C) :
  ⊢ logrel _ M α → logrel _ (Y M) (interp_Y E α).
Proof.
  simpl. iIntros "#HM".
  iLöb as "IH".
  rewrite {2}(interp_Y_app E α).
  iApply logrel_step_1.
  { econstructor. }
  iNext. iApply "HM".
  iApply "IH".
Qed.

Lemma logrel_nat_succ Γ (t : tm Γ tnat) α :
  ⊢ logrel_nat t α →
    logrel_nat (Succ t) (lift_map succ_ne α).
Proof.
  iLöb as "IH" forall (t α).
  iIntros "H".
  rewrite logrel_nat_unfold. iDestruct "H" as "[H1|H1]".
  + iDestruct "H1" as (n) "[Ht %Hn]".
    iRewrite "Ht". rewrite lift_map_unit.
    rewrite (logrel_nat_unfold (Succ _)). iLeft.
    iExists (S n). iSplit; eauto. iPureIntro.
    eapply step_clos_trans_0.
    { eapply step_close_Succ; eauto. }
    eapply step_clos_once.
    econstructor.
  + iDestruct "H1" as (β M' M'') "[Ht [%HM [%HM' H1]]]".
    rewrite (logrel_nat_unfold (Succ _)). iRight. compute[interp_ty] in β.
    iExists ( (lift_map succ_ne) β), (Succ M'), (Succ M'').
    repeat iSplit; eauto.
    * iRewrite "Ht".
      by rewrite lift_map_delay.
    * iPureIntro. eapply step_close_Succ; eauto.
    * iPureIntro. by econstructor.
    * iNext. by iApply "IH".
Qed.

Lemma logrel_nat_pred Γ (t : tm Γ tnat) α :
  ⊢ logrel_nat t α →
    logrel_nat (Pred t) (lift_map pred_ne α).
Proof.
  iLöb as "IH" forall (t α).
  iIntros "H".
  rewrite logrel_nat_unfold. iDestruct "H" as "[H1|H1]".
  + iDestruct "H1" as (n) "[Ht %Hn]".
    iRewrite "Ht". rewrite lift_map_unit.
    rewrite (logrel_nat_unfold (Pred _)). iLeft.
    iExists (pred n). iSplit; eauto. iPureIntro.
    eapply step_clos_trans_0.
    { eapply step_close_Pred; eauto. }
    eapply step_clos_once.
    econstructor.
  + iDestruct "H1" as (β M' M'') "[Ht [%HM [%HM' H1]]]".
    rewrite (logrel_nat_unfold (Pred _)). iRight. compute[interp_ty] in β.
    iExists (lift_map pred_ne β), (Pred M'), (Pred M'').
    repeat iSplit; eauto.
    * iRewrite "Ht".
      by rewrite lift_map_delay.
    * iPureIntro. by eapply step_close_Pred.
    * iPureIntro. by econstructor.
    * iNext. by iApply "IH".
Qed.

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
    iIntros (ss) "Hss". simpl.
    iIntros (N β) "HN".
    simp subst_tm. simp interp_tm.
    simpl.
    iApply logrel_step_0.
    { econstructor. }
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
    iIntros (ss) "#Hss". simpl.
    simp subst_tm interp_tm. simpl.
    iPoseProof (IHt1 with "Hss") as "H1".
    iPoseProof (IHt2 with "Hss") as "H2".
    iSimpl in "H1". iApply ("H1" with "H2").
  - (* Succ *)
    iIntros (ss) "#Hss". simpl.
    simp subst_tm interp_tm. simpl.
    iPoseProof (IHt with "Hss") as "H1".
    iSimpl in "H1".
    iApply (logrel_nat_succ with "H1").
  - (* Pred *)
    iIntros (ss) "#Hss". simpl.
    simp subst_tm interp_tm. simpl.
    iPoseProof (IHt with "Hss") as "H1".
    iSimpl in "H1".
    iApply (logrel_nat_pred with "H1").
  - (* Y *)
    iIntros (ss) "#Hss".
    simp subst_tm interp_tm. simpl.
    assert
      ((interp_Y (interp_ctx_of_subs2 ss) (interp_tm t (interp_ctx_of_subs2 ss))) ≡ (interp_Y (C:=[]) () (interp_tm t (interp_ctx_of_subs2 ss))))
    as ->.
    { f_equiv. apply (@interp_Y_const τ _ [] (interp_ctx_of_subs2 ss) ()). }
    iPoseProof ((logrel_Y _ τ (subst_tm t (subs_of_subs2 ss)) (interp_tm t (interp_ctx_of_subs2 ss)) ())) as "H".
    iApply "H". by iApply IHt.
Qed.

(** * Adequacy *)

Lemma logrel_adequacy (M : tm [] tnat) (n k : nat) :
  (⊢ logrel tnat M (ty_tick_k k (lift_unit n : interp_ty tnat)))
  → step_clos M k (Num n).
Proof.
  intros Hlog.
  cut (⊢ ▷^k ⌜step_clos M k (Num n)⌝ : siProp)%I.
  { intros HH.
    eapply siProp.pure_soundness.
    by eapply (laterN_soundness _ k). }

  iPoseProof Hlog as "H". clear Hlog. (* iRevert "H". *)
  (* iLöb as "IHl" forall (M); iIntros "#H". *)
  iInduction k as [|k] "IH" forall (M).
  - iSimpl in "H". rewrite logrel_nat_unfold.
    iDestruct "H" as "[H | H]".
    + iDestruct "H" as (m) "[Hunit %]".
      rewrite lift_unit_inj. by iDestruct "Hunit" as %->.
    + iDestruct "H" as (β M' M'') "(Hβ & %HM & %HM' & H)".
      simpl. iExFalso. by iApply lift_unit_delay_ne.
  - iSimpl in "H". rewrite logrel_nat_unfold.
    iDestruct "H" as "[H | H]".
    + iDestruct "H" as (n0) "[Heq1 %]". iExFalso.
      simpl. iExFalso. iApply (lift_unit_delay_ne _ n0).
      iRewrite -"Heq1". done.
    + iDestruct "H" as (β M' M'') "(Hβ & %HM & %HM' & H)".
      rewrite lift_delay_inj. iNext.
      iSpecialize ("IH" with "[-]").
      { iRewrite "Hβ". done. }
      iNext.
      iDestruct "IH" as %IH. iPureIntro.
      (* need some computations of step_clos *)
      eapply step_clos_trans; eauto.
      change (S k) with (1 + k). econstructor; eauto.
Qed.

Transparent lift_unit lift_delay.
