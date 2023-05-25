From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import base tactics classes modality_instances.
From iris.base_logic.lib Require Export own fancy_updates invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify reductions.


Section weakestpre.

  Fixpoint reifiers_ucmra {E} (rs : reifiers E) X `{!Cofe X} : ucmra :=
    match rs with
    | reifiers_nil => unitR
    | reifiers_cons _ stateF _ tail =>
        prodR (optionUR (exclR (stateF ♯ X)))
              (reifiers_ucmra tail X)
    end.

  Fixpoint of_state {E} (rs : reifiers E) X `{!Cofe X}:
    reifiers_state rs ♯ X → reifiers_ucmra rs X :=
    match rs return reifiers_state rs ♯ X → reifiers_ucmra rs X with
    | reifiers_nil => λ x, ()
    | reifiers_cons _ stateF _ tail => λ xy,
        let x : stateF ♯ X := xy.1 in
        let y : reifiers_state tail ♯ X := xy.2 in
        (Excl' x, of_state tail X y)
    end.

  #[export] Instance of_state_ne {E} (rs : reifiers E) X `{!Cofe X}:
    NonExpansive (of_state rs X).
  Proof.
    induction rs; simpl; first apply _.
    intros n [x1 y1] [x2 y2] [Hx Hy].
    solve_proper.
  Qed.
  #[export] Instance of_state_proper {E} (rs : reifiers E) X `{!Cofe X}:
    Proper ((≡) ==> (≡)) (of_state rs X).
  Proof. apply ne_proper, _. Qed.
  Lemma of_state_valid {E} (rs : reifiers E) X `{!Cofe X} σ :
    ✓ (of_state rs X σ).
  Proof.
    induction rs; simpl; first done.
    split; [done|eauto].
  Qed.
  Lemma of_state_agree' {E} (rs : reifiers E) X `{!Cofe X} σ σ' :
    (of_state rs X σ ≼ of_state rs X σ') → σ ≡ σ'.
  Proof.
    induction rs; simpl in *.
    { by destruct σ, σ'. }
    destruct σ as [σ1 σ2], σ' as [σ'1 σ'2]; simpl.
    rewrite prod_included /= Excl_included.
    intros [H1 Hs]. f_equiv; eauto.
  Qed.
  Lemma of_state_agree {E} (rs : reifiers E) X `{!Cofe X} σ σ' f
    `{!BiInternalEq PROP}:
    (of_state rs X σ ≡ of_state rs X σ' ⋅ f) ⊢@{PROP} σ ≡ σ'.
  Proof.
    iInduction rs as [|F stateF re tl] "IH" forall (f);
      simpl in *.
    { by destruct σ, σ'. }
    destruct σ as [σ1 σ2], σ' as [σ'1 σ'2]; simpl.
    destruct f as [f1 f2].
    rewrite -pair_op !prod_equivI /=.
    iIntros "[H1 #H2]". iSplit.
    - (* destruct f1 as [f1|]; rewrite option_equivI/=. *)
      (* rewrite excl_equivI) in "H1". *)
      admit.
    - iApply ("IH" with "H2").
  Admitted.

  Lemma of_state_update {E} (rs : reifiers E) X `{!Cofe X} σ σ' σ0 :
     ● of_state rs X σ ⋅ ◯ of_state rs X σ' ~~> ● of_state rs X σ0 ⋅ ◯ of_state rs X σ0.
  Proof.
    apply auth_update.
    induction rs; simpl in *.
    { apply unit_local_update. }
    destruct σ as [σ1 σ2], σ' as [σ'1 σ'2]; simpl.
    apply prod_local_update'.
    + apply option_local_update.
      apply exclusive_local_update. done.
    + apply IHrs.
  Qed.

  Context {E : opsInterp}.
  Variable (rs : reifiers E).
  Notation IT := (IT E).
  Notation ITV := (ITV E).
  Notation stateF := (reifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (reifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Notation reify := (reify rs).
  Notation istep := (istep rs).
  Notation isteps := (isteps rs).
  Notation sstep := (sstep rs).
  Notation ssteps := (ssteps rs).


  (** Ghost state for the state *)
  Class statePreG Σ := {
      statePreG_in :: inG Σ (authUR stateR);
    }.
  Class stateG (Σ : gFunctors) := {
      stateG_inG :: statePreG Σ;
      stateG_name : gname;
    }.
  Definition stateΣ : gFunctors := GFunctor (authUR stateR).
  Definition state_interp `{!stateG Σ} (σ : stateO) : iProp Σ :=
    (own stateG_name (● (of_state σ)))%I.
  Definition has_state `{!stateG Σ} (σ : stateO) : iProp Σ :=
    (own stateG_name (◯ (of_state σ)))%I.
  #[export] Instance state_interp_ne `{!stateG Σ} : NonExpansive state_interp.
  Proof. solve_proper. Qed.
  #[export] Instance has_state_ne `{!stateG Σ} : NonExpansive state_interp.
  Proof. solve_proper. Qed.

  Lemma new_state_interp σ `{!invGS_gen hlc Σ, !statePreG Σ} :
    (⊢ |==> ∃ `{!stateG Σ}, state_interp σ ∗ has_state σ : iProp Σ)%I.
  Proof.
    iMod (own_alloc ((● (of_state σ)) ⋅ (◯ (of_state σ)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_2; eauto. apply of_state_valid. }
    pose (sg := {| stateG_inG := _; stateG_name := γ |}).
    iModIntro. iExists sg. by iFrame.
  Qed.
  #[export] Instance subG_stateΣ {Σ} : subG stateΣ Σ → statePreG Σ.
  Proof. solve_inG. Qed.

  Context `{!invGS_gen hlc Σ} `{!stateG Σ}.
  Notation iProp := (iProp Σ).

  (** Weakest precondition *)
  Program Definition wp_pre (Φ : ITV → iProp) (self : IT -n> iProp) : IT -n> iProp
    := λne α,
      ((∃ αv, IT_to_V α ≡ Some αv ∧ Φ αv)
     ∨ (IT_to_V α ≡ None ∧ ∀ σ, state_interp σ -∗
           (∃ α' σ', istep α σ α' σ')  (* α is safe *)
             ∧ (∀ σ' β, istep α σ β σ' ={⊤}[∅]▷=∗ state_interp σ' ∗ self β)))%I.
  Next Obligation. solve_proper. Qed.

  #[local] Instance wp_pre_contractive Φ : Contractive (wp_pre Φ).
  Proof. unfold wp_pre. solve_contractive. Qed.
  Definition wp α Φ := fixpoint (wp_pre Φ) α.
  Lemma wp_unfold α Φ :
    wp α Φ ≡
       ((∃ αv, IT_to_V α ≡ Some αv ∧ Φ αv)
     ∨ (IT_to_V α ≡ None ∧ ∀ σ, state_interp σ -∗
                    (∃ α' σ', istep α σ α' σ')  (* α is safe *)
                  ∧ (∀ σ' β, istep α σ β σ' ={⊤}[∅]▷=∗ state_interp σ' ∗ wp β Φ)))%I.
  Proof. apply (fixpoint_unfold (wp_pre Φ) _). Qed.

  Notation "'WP' α {{ β , Φ } }" := (wp α (λ β, Φ))
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  β ,  Φ  } }") : bi_scope.

  Notation "'WP' α {{ Φ } }" := (wp α Φ)
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  Φ  } }") : bi_scope.

  #[export] Instance wp_ne n :
    Proper ((dist n) ==> (pointwise_relation _ (dist n)) ==> (dist n)) wp.
  Proof.
    intros α1 α2 Ha Φ1 Φ2 Hp.
    revert α1 α2 Ha.
    induction (lt_wf n) as [n _ IH]=>α1 α2 Ha.
    rewrite !wp_unfold.
    f_equiv; first by repeat f_equiv.
    f_equiv; first  solve_proper.
    f_equiv. f_equiv. f_equiv.
    f_equiv; first solve_proper.
    f_equiv. f_equiv. f_equiv. f_equiv.
    f_equiv; first solve_proper. f_equiv.
    f_contractive. f_equiv. f_equiv.
    apply IH; eauto. f_equiv.
    eapply dist_le; [apply Hp|lia].
  Qed.
  #[export] Instance wp_proper :
    Proper ((≡) ==> (pointwise_relation _ (≡)) ==> (≡)) wp.
  Proof.
    intros α1 α2 Ha Φ1 Φ2 Hp.
    apply equiv_dist=>n.
    apply wp_ne.
    - by apply equiv_dist.
    - intros v. by apply equiv_dist, Hp.
  Qed.

  Lemma wp_val α αv Φ :
    IT_to_V α ≡ Some αv ⊢ Φ αv -∗ WP α {{ Φ }}.
  Proof.
    iIntros "Ha Hp". rewrite wp_unfold. iLeft.
    iExists αv. by iFrame.
  Qed.

  Lemma wp_val_inv α αv Φ `{!NonExpansive Φ} :
    IT_to_V α ≡ Some αv ⊢ WP α {{ Φ }} -∗ Φ αv.
  Proof.
    iIntros "Ha". rewrite wp_unfold.
    iDestruct 1 as "[H|[Ha2 H]]".
    + iDestruct "H" as (αv2) "[Ha2 Hp]".
      iRewrite "Ha" in "Ha2".
      iPoseProof (option_equivI with "Ha2") as "Ha".
      by iRewrite "Ha".
    + iRewrite "Ha" in "Ha2".
      iPoseProof (option_equivI with "Ha2") as "Ha".
      done.
  Qed.

  Lemma wp_val_inv' α αv Φ `{!NonExpansive Φ} :
    IT_to_V α ≡ Some αv → WP α {{ Φ }} ⊢ Φ αv.
  Proof.
    intros Hv. iApply wp_val_inv. eauto.
  Qed.

  Lemma wp_bind (f : IT → IT) `{!IT_hom f} (α : IT) Φ `{!NonExpansive Φ} :
    WP α {{ βv, WP (f (IT_of_V βv)) {{ βv, Φ βv }} }} ⊢ WP (f α) {{ Φ }}.
  Proof.
    assert (NonExpansive (λ βv0, WP f (IT_of_V βv0) {{ βv1, Φ βv1 }})%I).
    { solve_proper. }
    iIntros "H". iLöb as "IH" forall (α).
    rewrite (wp_unfold (f _)).
    destruct (IT_to_V (f α)) as [βv|] eqn:Hfa.
    - iLeft. iExists βv. iSplit; first done.
      assert (is_Some (IT_to_V α)) as [αv Ha].
      { apply (IT_hom_val_inv _ f). rewrite Hfa.
        done. }
      rewrite wp_val_inv'; last first.
      { by rewrite Ha. }
      iApply wp_val_inv.
      { rewrite -Hfa. done. }
      iAssert (α ≡ IT_of_V αv)%I as "Hav".
      { iApply internal_eq_sym.
        iApply IT_of_to_V. by rewrite Ha. }
      iRewrite "Hav". done.
    - iRight. iSplit; eauto.
      iIntros (σ) "Hs". iSplit.
      { (* safety *)
        rewrite wp_unfold.
        iDestruct "H" as "[H|[Ha H]]".
        - iDestruct "H" as (αv) "[Ha H]".
          iAssert (IT_of_V αv ≡ α)%I with "[Ha]" as "Hav".
          { iApply IT_of_to_V. done. }
          iRewrite "Hav" in "H".
          rewrite wp_unfold. rewrite Hfa.
          iDestruct "H" as "[H | [_ H]]".
          { iDestruct "H" as (?) "[H _]".
            iExFalso. iApply (option_equivI with "H"). }
          iSpecialize ("H" with "Hs").
          iDestruct "H" as "[$ _]".
        - iSpecialize ("H" with "Hs").
          iDestruct "H" as "[H _]".
          iDestruct "H" as (α1 σ1) "Hst".
          iExists (f α1),σ1. iApply (istep_hom with "Hst"). }
      (* preservation *)
      iIntros (σ' β) "#Hst".
      iAssert (istep (f α) σ β σ')%I as "Hst'".
      { done. }
      rewrite {1}istep_hom_inv. iDestruct "Hst" as "[%Ha | Hst]".
      (* looking at whether α is a value *)
      + destruct Ha as [av Hav].
        iAssert (IT_of_V av ≡ α)%I with "[]" as "Hav".
        { iApply IT_of_to_V. by rewrite Hav. }
        rewrite wp_val_inv'; last first.
        { by rewrite Hav. }
        rewrite wp_unfold. iRewrite "Hav" in "H". rewrite Hfa.
        iDestruct "H" as "[H | [_ H]]".
        { iDestruct "H" as (?) "[H _]".
          iExFalso. iApply (option_equivI with "H"). }
        iSpecialize ("H" with "Hs").
        iDestruct "H" as "[_ H]".
        by iApply "H".
      + iDestruct "Hst" as "[Ha Hst]".
        iDestruct "Hst" as (α') "[Hst Hb]".
        rewrite wp_unfold.
        iRewrite "Ha" in "H".
        iDestruct "H" as "[H | [_ H]]".
        { iDestruct "H" as (?) "[H _]".
            iExFalso. iApply (option_equivI with "H"). }
        iSpecialize ("H" with "Hs").
        iDestruct "H" as "[_ H]".
        iSpecialize ("H" with "Hst").
        iMod "H" as "H". iModIntro. iNext.
        iMod "H" as "[$ H]". iModIntro.
        iRewrite "Hb". by iApply "IH".
  Qed.

  Lemma wp_wand α Φ Ψ :
    (WP α {{ Ψ }}) -∗ (∀ v, Ψ v -∗ Φ v) -∗ WP α {{ Φ }}.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (α).
    rewrite !wp_unfold.
    iDestruct "H1" as "[H1 | H1]".
    - iLeft. iDestruct "H1" as (av) "[H1 H]".
      iExists _. iSplit; eauto. by iApply "H2".
    - iRight. iDestruct "H1" as "[H1 H]".
      iSplit; first by eauto. iIntros (σ) "Hs".
      iDestruct ("H" with "Hs") as "[$ H]".
      iIntros (σ' β) "Hst". iMod ("H" with "Hst") as "H".
      iModIntro. iNext. iMod ("H") as "[$ H]".
      iModIntro. by iApply ("IH" with "H").
  Qed.

  Lemma wp_tick α Φ :
    ▷ WP α {{ Φ }} ⊢ WP (Tick α) {{ Φ }}.
  Proof.
    iIntros "H". rewrite (wp_unfold (Tick _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Tau. }
    iIntros (σ) "Hs". iSplit.
    - iExists α,σ. iLeft. eauto.
    - iIntros (σ' β) "Hst". rewrite istep_tick.
      iDestruct "Hst" as "[Hb Hs']".
      iRewrite -"Hs'". iFrame "Hs".
      iApply step_fupd_intro; first solve_ndisj.
      iNext. iRewrite "Hb". by iFrame.
  Qed.

  Lemma wp_reify op i ko β σ σ' Φ :
    reify (Vis op i ko) σ ≡ (σ', Tick β) →
    has_state σ -∗ (has_state σ' -∗ ▷ WP β {{ Φ }})
          -∗ WP (Vis op i ko) {{ Φ }}.
  Proof.
    intros Hreify. iIntros "Hs Hb".
    rewrite (wp_unfold (Vis _ _ _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Vis. }
    iIntros (σ0) "Hσ0".
    (* we know what the real state is *)
    iAssert (σ ≡ σ0)%I with "[Hs Hσ0]" as "#Hss".
    { rewrite /has_state /state_interp.
      iCombine "Hσ0 Hs" as "Hs".
      iDestruct (own_valid with "Hs") as "Hs".
      rewrite auth_both_validI.
      iDestruct "Hs" as "[Hs _]".
      iDestruct "Hs" as (f) "Hs".
      rewrite of_state_agree.
      by iApply (internal_eq_sym (σ0 : stateO) (σ : stateO)). }
    iSplit.
    { (* it is safe *)
      iExists β,σ'. iRight. iExists op,i,ko.
      iRewrite -"Hss". eauto. }
    iIntros (σ0' α0) "Hst". rewrite istep_vis.
    iRewrite -"Hss" in "Hst".
    iAssert (▷ (α0 ≡ β) ∧ σ0' ≡ σ')%I with "[Hst]" as "[Ha1 Hss']".
    { rewrite Hreify.
      iPoseProof (prod_equivI with "Hst") as "[Ha Hs]". simpl.
      iSplit.
      + iNext. by iApply internal_eq_sym.
      + by iApply internal_eq_sym.  }
    iRewrite "Hss'".
    iMod (own_update_2 with "Hσ0 Hs") as "[Hs0 Hs]".
    { apply (of_state_update _ _ _ _ σ'). }
    iSpecialize ("Hb" with "Hs"). iFrame "Hs0".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl".
    iNext. iMod "Hcl" as "_".
    iRewrite "Ha1". done.
  Qed.

  Lemma wp_subreify {F} {stateF} (op : opid F) (i : Ins (F op) ♯ IT)
    (re : reify_eff F stateF) `{!subReifier re rs rest}
    (ko : Outs (E (subEff_opid op)) ♯ IT -n> laterO IT)
    (o : Outs (F op) ♯ IT)
    (σ1 σ1' : stateF ♯ IT) (σr : rest ♯ IT) α Φ :
    re op IT _ (i,σ1) ≡ Some (o,σ1') →
    ko (subEff_conv_outs o) ≡ Next α →
    has_state (subState_conv_state σr σ1) -∗ (has_state (subState_conv_state σr σ1')
          -∗ ▷ WP α {{ Φ }}) -∗
       WP (Vis (subEff_opid op) (subEff_conv_ins i) ko) {{ Φ }}.
  Proof.
    intros Hre Hko. iIntros "Hst H".
    iApply (wp_reify _ _ _ α _  (subState_conv_state σr σ1')  with "Hst H").
    rewrite reify_vis_eq.
    { rewrite Tick_eq. rewrite -Hko.
      reflexivity. }
    rewrite subR_reify. rewrite Hre. reflexivity.
  Qed.

  Lemma wp_istep α σ β σ' Ψ :
    ⊢ istep α σ β σ' -∗ state_interp σ -∗ WP α {{ Ψ }}
    ={⊤}[∅]▷=∗ state_interp σ' ∗ WP β {{ Ψ }}.
  Proof.
    iIntros "Hstep Hs H".
    rewrite (wp_unfold α). iDestruct "H" as "[H|[Ha H]]".
    - iExFalso. iDestruct "H" as (αv) "[H _]".
      iApply (istep_ITV with "H Hstep").
    - iSpecialize ("H" with "Hs"). iDestruct "H" as "[_ H]".
      iApply ("H" with "Hstep").
  Qed.

  Lemma wp_isteps k α σ β σ' Ψ :
    ⊢ isteps α σ β σ' k -∗ state_interp σ -∗ WP α {{ Ψ }}
    ={⊤}[∅]▷=∗^k state_interp σ' ∗ WP β {{ Ψ }}.
  Proof.
    iInduction k as [|k] "IH" forall (α σ).
    - rewrite isteps_0. iIntros "[Ha Hs]".
      simpl. iRewrite "Ha". iRewrite "Hs".
      eauto with iFrame.
    - rewrite isteps_S. iDestruct 1 as (α1 σ1) "[Hstep Hsts]".
      iIntros "Hst H". iSimpl.
      iPoseProof (wp_istep with "Hstep Hst H") as "H".
      iMod "H" as "H". iModIntro. iNext.
      iMod "H" as "[Hs H]". iModIntro.
      iApply ("IH" with "Hsts Hs H").
  Qed.

  Lemma wp_ssteps α σ β σ' k Ψ :
    ssteps α σ β σ' k →
    state_interp σ ∗ WP α {{ Ψ }}
              ⊢ |={⊤}[∅]▷=>^k state_interp σ' ∗ WP β {{ Ψ }}.
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (isteps α σ β σ' k) as "Hst".
    { by iApply ssteps_isteps. }
    iApply (wp_isteps with "Hst Hs HIC").
  Qed.

  Lemma wp_ssteps_isafe α σ β σ' k Ψ :
    ssteps α σ β σ' k →
    state_interp σ ∗ WP α {{ Ψ }}
                 ⊢ |={⊤}[∅]▷=>^k ⌜is_Some (IT_to_V β)⌝ ∨ ∃ β2 σ2, istep β σ' β2 σ2.
  Proof.
    intros Hst. rewrite wp_ssteps//.
    apply step_fupdN_mono.
    iIntros "[Hst H]".
    rewrite wp_unfold. iDestruct "H" as "[H | [Hb H]]".
    - iLeft. iDestruct "H" as (av) "[H _]".
      destruct (IT_to_V β) as [βv|]; first by eauto.
      iExFalso. iApply (option_equivI with "H").
    - iRight. iDestruct ("H" with "Hst") as "[$ _]".
  Qed.

  Lemma wp_ssteps_val α σ βv σ' k Ψ `{!NonExpansive Ψ} :
    ssteps α σ (IT_of_V βv) σ' k →
    state_interp σ ∗ WP α {{ Ψ }}
                 ⊢ |={⊤}[∅]▷=>^k Ψ βv.
  Proof.
    intros Hst. rewrite wp_ssteps//.
    apply step_fupdN_mono.
    iIntros "[Hst H]".
    rewrite wp_unfold. iDestruct "H" as "[H | [Hb H]]".
    - iDestruct "H" as (av) "[H HH]".
      rewrite IT_to_of_V. iPoseProof (option_equivI with "H") as "H".
      by iRewrite "H".
    - rewrite IT_to_of_V.
      iExFalso. iApply (option_equivI with "Hb").
  Qed.

End weakestpre.

Arguments wp {_} rs {_ _ _ _} α Φ.
Arguments has_state {E} {_ _ _} σ.
Arguments stateG {E} rs Σ.
Arguments stateΣ {E} rs.

Notation "'WP@{' re } α {{ β , Φ } }" := (wp re α (λ β, Φ))
    (at level 20, re, α, Φ at level 200,
     format "'WP@{' re }  α  {{  β ,  Φ  } }") : bi_scope.

Notation "'WP@{' re } α {{ Φ } }" := (wp re α Φ)
    (at level 20, re, α, Φ at level 200,
     format "'WP@{' re }  α  {{  Φ  } }") : bi_scope.

Lemma wp_adequacy E (rs : reifiers E)
  α σ βv σ' k (ψ : (ITV E) → Prop) :
  ssteps rs α σ (IT_of_V βv) σ' k →
  (∀ `{H1 : !invGS_gen hlc Σ} `{H2: !stateG rs Σ},
      ∃ Φ, NonExpansive Φ ∧ (∀ βv, Φ βv ⊢ ⌜ψ βv⌝)
      ∧ (has_state σ ⊢ WP@{rs} α {{ Φ }})%I)  →
  ψ βv.
Proof.
  intros Hst Hprf.
  pose (Σ :=  #[invΣ; stateΣ rs]).
  cut (⊢ ⌜ψ βv⌝ : iProp Σ)%I.
  { intros HH. eapply uPred.pure_soundness; eauto. }
  eapply (step_fupdN_soundness_lc' _ (S k) k).
  intros lc Hinv. iIntros "Hk".
  rewrite step_fupdN_S_fupd. simpl.
  iMod (new_state_interp rs σ) as (sg) "[Hs Hs2]".
  destruct (Hprf lc Σ Hinv sg) as (Φ & HΦ & HΦψ & Hprf').
  iPoseProof (Hprf' with "Hs2") as "Hic".
  iPoseProof (wp_ssteps with "[$Hs $Hic]") as "Hphi".
  { eassumption. }
  iApply fupd_mask_intro; first solve_ndisj.
  iIntros "Hcl". iNext. iMod "Hcl" as "_". iModIntro.
  iApply (step_fupdN_mono with "Hphi").
  rewrite bi.sep_elim_r. rewrite -HΦψ.
  rewrite wp_val_inv'; eauto. apply IT_to_of_V.
Qed.
