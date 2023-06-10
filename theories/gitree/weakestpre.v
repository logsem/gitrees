From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import base tactics classes modality_instances.
From iris.base_logic.lib Require Export own fancy_updates invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify reductions.


Definition mega_fupdN k `{!invGS_gen hlc Σ}: iProp Σ → iProp Σ :=
  Nat.iter k (λ P, |={⊤,∅}=> |={∅}▷=>^2 |={∅,⊤}=> P)%I.
#[global] Instance mega_fupdN_ne k `{!invGS_gen hlc Σ} : NonExpansive (mega_fupdN k).
Proof. induction k; solve_proper. Qed.
#[global] Instance mega_fupdN_proper k `{!invGS_gen hlc Σ} :
  Proper ((≡) ==> (≡)) (mega_fupdN k).
Proof. induction k; solve_proper. Qed.
Lemma mega_fupdN_mono k `{!invGS_gen hlc Σ} P Q :
  (P ⊢ Q) →
  mega_fupdN k P ⊢ mega_fupdN k Q.
Proof.
  induction k; first by eauto.
  intros HPQ. simpl.
  do 8 f_equiv. by apply IHk.
Qed.
Lemma mega_fupdN_S_fupd n `{!invGS_gen hlc Σ} P :
  mega_fupdN (S n) (|={⊤}=> P) ⊢ mega_fupdN (S n) P.
Proof.
  unfold mega_fupdN.
  rewrite !Nat.iter_succ_r.
  apply mega_fupdN_mono.
  rewrite -(fupd_trans _ _ ⊤ P) //.
Qed.
Lemma mega_fupdN_soundness_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n :
  (∀ `{Hinv: !invGS_gen hlc Σ}, ⊢ mega_fupdN n P) →
  ⊢ P.
Proof.
  intros HP.
  eapply (fupd_soundness_lc (2*n) ⊤ ⊤ P); [apply _..|].
  iIntros (Hinv) "Hlc".
  iPoseProof HP as "-#Hupd". clear HP.
  iInduction n as [|n] "IH".
  - by iModIntro.
  - rewrite Nat.mul_succ_r.
    iDestruct "Hlc" as "[Hn [Hone Htwo]]".
    iEval (simpl) in "Hupd".
    iMod "Hupd".
    iMod "Hupd".
    iMod (lc_fupd_elim_later with "Hone Hupd") as "Hupd".
    iMod "Hupd".
    iMod "Hupd".
    iMod (lc_fupd_elim_later with "Htwo Hupd") as "> Hupd".
    iMod "Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

Section weakestpre.

  Definition gReifiers_ucmra {n} (rs : gReifiers n) X `{!Cofe X} : ucmra :=
    discrete_funUR (λ (i : fin n), optionUR (exclR (sReifier_state (rs !!! i) ♯ X))).

  Definition of_state {n} (rs : gReifiers n) {X} `{!Cofe X}
    (st : gReifiers_state rs ♯ X) : gReifiers_ucmra rs X :=
    λ i, Excl' (fstO (gState_decomp i st)).

  Definition of_idx {n} (i : fin n) {rs : gReifiers n} {X} `{!Cofe X}
    (st : sReifier_state (rs !!! i) ♯ X) : gReifiers_ucmra rs X.
  Proof.
    simple refine (λ j, if (decide (j = i)) then _ else None).
    simpl. rewrite e. exact (Excl' st).
  Defined.

  #[export] Instance of_state_ne {n} (rs : gReifiers n) X `{!Cofe X}:
    NonExpansive (of_state rs (X:=X)).
  Proof. solve_proper. Qed.
  #[export] Instance of_state_proper {n} (rs : gReifiers n) X `{!Cofe X}:
    Proper ((≡) ==> (≡)) (of_state rs (X:=X)).
  Proof. apply ne_proper, _. Qed.

  Lemma of_state_valid {n} (rs : gReifiers n) X `{!Cofe X}
    (σ : gReifiers_state rs ♯ X) :
    ✓ (of_state rs σ).
  Proof. intro; done. Qed.
  Lemma of_state_agree' {n} (rs : gReifiers n) X `{!Cofe X}
    (σ σ' : gReifiers_state rs ♯ X) :
    (of_state rs σ ≼ of_state rs σ') → σ ≡ σ'.
  Proof.
    induction rs; simpl in *.
    { by destruct σ, σ'. }
    destruct σ as [σ1 σ2], σ' as [σ'1 σ'2]; simpl.
    intros Hinc.
    assert (∀ (i : fin (S n)), of_state (gReifiers_cons s rs) (σ1, σ2) i ≼ of_state (gReifiers_cons s rs) (σ'1, σ'2) i) as H.
    { by apply discrete_fun_included_spec. }
    unfold of_state in H. revert H.
    setoid_rewrite Excl_included. intros H.
    f_equiv.
    - apply (H 0%fin).
    - eapply IHrs.
      apply discrete_fun_included_spec.
      intros x. unfold of_state.
      rewrite Excl_included. apply (H (FS x)).
  Qed.

  (* Lemma of_state_agree {Σ} {n} (rs : gReifiers n) X `{!Cofe X} σ σ' f : *)
  (*   (of_state rs X σ ≡ of_state rs X σ' ⋅ f ⊢@{iProp Σ} σ ≡ σ')%I. *)
  (* Proof. *)
  (*   iInduction rs as [|F stateF re tl] "IH" forall (f); *)
  (*     simpl in *. *)
  (*   { by destruct σ, σ'. } *)
  (*   destruct σ as [σ1 σ2], σ' as [σ'1 σ'2]; simpl. *)
  (*   destruct f as [f1 f2]. *)
  (*   rewrite -pair_op !prod_equivI /=. *)
  (*   iIntros "[H1 #H2]". iSplit. *)
  (*   - destruct f1 as [f1|]; rewrite option_equivI/= excl_equivI//. *)
  (*   - iApply ("IH" with "H2"). *)
  (* Qed. *)

  (* Lemma of_state_update {E} (rs : reifiers E) X `{!Cofe X} σ σ' σ0 : *)
  (*    ● of_state rs X σ ⋅ ◯ of_state rs X σ' ~~> ● of_state rs X σ0 ⋅ ◯ of_state rs X σ0. *)
  (* Proof. *)
  (*   apply auth_update. *)
  (*   induction rs; simpl in *. *)
  (*   { apply unit_local_update. } *)
  (*   destruct σ as [σ1 σ2], σ' as [σ'1 σ'2]; simpl. *)
  (*   apply prod_local_update'. *)
  (*   + apply option_local_update. *)
  (*     apply exclusive_local_update. done. *)
  (*   + apply IHrs. *)
  (* Qed. *)
  Context {n : nat} (rs : gReifiers n).
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Notation stateF := (gReifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs (X:=IT)).
  Notation reify := (reify rs).
  Notation istep := (istep rs).
  Notation isteps := (isteps rs).
  Notation sstep := (sstep rs).
  Notation ssteps := (ssteps rs).

  Implicit Type op : opid F.
  Implicit Type α β : IT.



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
  Definition has_full_state `{!stateG Σ} (σ : stateO) : iProp Σ :=
    (own stateG_name (◯ (of_state σ)))%I.
  Definition has_state_idx `{!stateG Σ} (i : fin n)
    (σ : sReifier_state (rs !!! i) ♯ IT) : iProp Σ :=
    (own stateG_name (◯ (of_idx i σ)))%I.
  #[export] Instance state_interp_ne `{!stateG Σ} : NonExpansive state_interp.
  Proof. solve_proper. Qed.
  #[export] Instance has_full_ne `{!stateG Σ} : NonExpansive has_full_state.
  Proof. solve_proper. Qed.

  Lemma new_state_interp σ `{!invGS_gen hlc Σ, !statePreG Σ} :
    (⊢ |==> ∃ `{!stateG Σ}, state_interp σ ∗ has_full_state σ : iProp Σ)%I.
  Proof.
    iMod (own_alloc ((● (of_state σ)) ⋅ (◯ (of_state σ)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_2; eauto. apply of_state_valid. }
    pose (sg := {| stateG_inG := _; stateG_name := γ |}).
    iModIntro. iExists sg. by iFrame.
  Qed.
  (* Lemma state_interp_has_state_agree σ1 σ2 `{!stateG Σ} : *)
  (*   state_interp σ1 -∗ has_state σ2 -∗ σ1 ≡ σ2. *)
  (* Proof. *)
  (*   iIntros "H1 H2". *)
  (*   iDestruct (own_valid_2 with "H1 H2") as "Hs". *)
  (*   rewrite auth_both_validI. *)
  (*   iDestruct "Hs" as "[Hs _]". *)
  (*   iDestruct "Hs" as (f) "Hs". *)
  (*   by rewrite of_state_agree. *)
  (* Qed. *)
  (* Lemma state_interp_has_state_update σ σ1 σ2 `{!stateG Σ} : *)
  (*   state_interp σ1 -∗ has_state σ2 ==∗ state_interp σ ∗ has_state σ. *)
  (* Proof. *)
  (*   iIntros "H1 H2". *)
  (*   iMod (own_update_2 with "H1 H2") as "H". *)
  (*   { apply (of_state_update _ _ _ _ σ). } *)
  (*   iDestruct "H" as "[$ $]". done. *)
  (* Qed. *)

  #[export] Instance subG_stateΣ {Σ} : subG stateΣ Σ → statePreG Σ.
  Proof. solve_inG. Qed.

  Context `{!invGS_gen hlc Σ} `{!stateG Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  (** Weakest precondition *)
  Program Definition wp_pre (Φ : ITV → iProp) (self : coPsetO -n> IT -n> iProp)
    : coPsetO -n> IT -n> iProp
    := λne E α,
      ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E}=> Φ αv)
     ∨ (IT_to_V α ≡ None ∧ ∀ σ, state_interp σ ={E,∅}=∗
           (∃ α' σ', istep α σ α' σ')  (* α is safe *)
             ∧ (∀ σ' β, istep α σ β σ' ={∅}▷=∗^2 |={∅,E}=> state_interp σ' ∗ self E β)))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    intros ? ? ? E1 E2 ->.
    solve_proper.
  Qed.

  #[local] Instance wp_pre_contractive Φ : Contractive (wp_pre Φ).
  Proof.
    unfold wp_pre.
    intros m s1 s2 Hs E1 a. simpl.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_contractive. solve_proper.
    (* solve_contractive. *)
  Qed.
  Definition wp α E Φ := fixpoint (wp_pre Φ) E α.
  Lemma wp_unfold E' α Φ :
    wp α E' Φ ≡
       ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E'}=> Φ αv)
     ∨ (IT_to_V α ≡ None ∧ ∀ σ, state_interp σ ={E',∅}=∗
                    (∃ α' σ', istep α σ α' σ')  (* α is safe *)
                  ∧ (∀ σ' β, istep α σ β σ' ={∅}▷=∗^2 |={∅,E'}=> state_interp σ' ∗ wp β E' Φ)))%I.
  Proof. apply (fixpoint_unfold (wp_pre Φ) _). Qed.

  Notation "'WP' α @ E {{ Φ } }" := (wp α E Φ)
    (at level 20, α, Φ at level 200, only parsing) : bi_scope.

  Notation "'WP' α @ E {{ v , Q } }" := (wp α E (λ v, Q))
    (at level 20, α, Q at level 200,
       format "'[hv' 'WP'  α  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  Notation "'WP' α {{ β , Φ } }" := (wp α ⊤ (λ β, Φ))
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  β ,  Φ  } }") : bi_scope.

  Notation "'WP' α {{ Φ } }" := (wp α ⊤ Φ)
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  Φ  } }") : bi_scope.

  #[export] Instance wp_ne m :
    Proper ((dist m) ==> (dist m) ==> (pointwise_relation _ (dist m)) ==> (dist m)) wp.
  Proof.
    intros α1 α2 Ha E1 E2 HE Φ1 Φ2 Hp.
    assert (E1 = E2) as ->.
    { apply HE. }
    revert α1 α2 Ha.
    induction (lt_wf m) as [m _ IH]=>α1 α2 Ha.
    rewrite !wp_unfold.
    f_equiv; first by repeat f_equiv.
    f_equiv; first  solve_proper.
    f_equiv. f_equiv. f_equiv.
    f_equiv.
    f_equiv; first solve_proper.
    f_equiv. f_equiv. f_equiv. f_equiv.
    f_equiv; first solve_proper. simpl.
    f_equiv.
    f_contractive. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv. f_equiv.
    apply IH; eauto. f_equiv.
    eapply dist_le; [apply Hp|lia].
  Qed.
  #[export] Instance wp_proper :
    Proper ((≡) ==> (≡) ==> (pointwise_relation _ (≡)) ==> (≡)) wp.
  Proof.
    intros α1 α2 Ha E1 E2 HE Φ1 Φ2 Hp.
    apply equiv_dist=>m.
    apply wp_ne.
    - by apply equiv_dist.
    - by apply equiv_dist.
    - intros v. by apply equiv_dist, Hp.
  Qed.

  Lemma wp_val' α αv Φ E1 :
    IT_to_V α ≡ Some αv ⊢ (|={E1}=> Φ αv) -∗ WP α @ E1 {{ Φ }}.
  Proof.
    iIntros "Ha Hp". rewrite wp_unfold. iLeft.
    iExists αv. by iFrame.
  Qed.
  Lemma wp_val α αv Φ E1 `{!IntoVal α αv}:
    (|={E1}=> Φ αv) ⊢ WP α @ E1 {{ Φ }}.
  Proof.
    iIntros "Hp". rewrite wp_unfold. iLeft.
    iExists αv. rewrite -IT_to_of_V into_val. by iFrame.
  Qed.

  Lemma wp_val_inv' α αv Φ `{!NonExpansive Φ} E1 :
    IT_to_V α ≡ Some αv ⊢ WP α @ E1 {{ Φ }} ={E1}=∗ Φ αv.
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

  Lemma wp_val_inv α αv Φ `{!NonExpansive Φ} E1  `{!IntoVal α αv} :
    WP α @ E1 {{ Φ }} ⊢ |={E1}=> Φ αv.
  Proof.
    iApply wp_val_inv'. iPureIntro.
    rewrite -IT_to_of_V into_val//.
  Qed.

  Lemma fupd_wp E1 α Φ `{NonExpansive Φ} :
    (|={E1}=> WP α @ E1 {{ Φ }}) ⊢ WP α @ E1 {{ Φ }}.
  Proof.
    rewrite wp_unfold. iIntros "H".
    destruct (IT_to_V α) as [αv|] eqn:Ha.
    { iLeft. iExists αv. iSplit; eauto.
      iMod "H" as "H". iDestruct "H" as "[H|H]".
      - iDestruct "H" as (βv) "[H H1]".
        iPoseProof (option_equivI with "H") as "H".
        by iRewrite "H".
      - iDestruct "H" as "[H _]".
        iPoseProof (option_equivI with "H") as "H".
        done. }
    iRight. iSplit; eauto.
    iIntros (σ) "Hs". iMod "H" as "H".
    iDestruct "H" as "[H|H]".
    - iDestruct "H" as (?) "[H _]".
      iPoseProof (option_equivI with "H") as "H".
      done.
    - iDestruct "H" as "[_ H]".
      iMod ("H" with "Hs") as "[H1 H2]".
      iModIntro. by iFrame.
  Qed.

  Lemma wp_wand α E1 Φ Ψ :
    (WP α @ E1 {{ Ψ }}) -∗ (∀ v, Ψ v ={E1}=∗ Φ v) -∗ WP α @ E1 {{ Φ }}.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (α).
    rewrite !wp_unfold.
    iDestruct "H1" as "[H1 | H1]".
    - iLeft. iDestruct "H1" as (av) "[H1 H]".
      iExists _. iSplit; eauto. iMod "H" as "H".
      by iApply "H2".
    - iRight. iDestruct "H1" as "[H1 H]".
      iSplit; first by eauto. iIntros (σ) "Hs".
      iMod ("H" with "Hs") as "[$ H]".
      iModIntro. iIntros (σ' β) "Hst". iMod ("H" with "Hst") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "H". iModIntro.
      iNext.
      iMod "H" as "H". iModIntro.
      iMod ("H") as "[$ H]".
      iModIntro. by iApply ("IH" with "H").
  Qed.

  Lemma wp_fupd E1 α Φ : WP α @ E1 {{ v, |={E1}=> Φ v }} ⊢ WP α @ E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply (wp_wand with "H"); auto.
  Qed.

  Lemma wp_bind (f : IT → IT) `{!IT_hom f} (α : IT) Φ `{!NonExpansive Φ} E1 :
    WP α @ E1 {{ βv, WP (f (IT_of_V βv)) @ E1 {{ βv, Φ βv }} }} ⊢ WP (f α) @ E1 {{ Φ }}.
  Proof.
    assert (NonExpansive (λ βv0, WP f (IT_of_V βv0) @ E1 {{ βv1, Φ βv1 }})%I).
    { solve_proper. }
    iIntros "H". iLöb as "IH" forall (α).
    rewrite (wp_unfold _ (f _)).
    destruct (IT_to_V (f α)) as [βv|] eqn:Hfa.
    - iLeft. iExists βv. iSplit; first done.
      assert (is_Some (IT_to_V α)) as [αv Ha].
      { apply (IT_hom_val_inv _ f). rewrite Hfa.
        done. }
      assert (IntoVal α αv).
      { apply IT_of_to_V'. by rewrite Ha. }
      rewrite wp_val_inv.
      iApply wp_val_inv.
      rewrite IT_of_to_V'; last by rewrite -Ha.
      rewrite IT_of_to_V'; last by rewrite -Hfa.
      by iApply fupd_wp.
    - iRight. iSplit; eauto.
      iIntros (σ) "Hs".
      rewrite wp_unfold.
      iDestruct "H" as "[H | H]".
      + iDestruct "H" as (αv) "[Hav H]".
        iPoseProof (IT_of_to_V with "Hav") as "Hav".
        iMod "H" as "H". rewrite wp_unfold.
        iDestruct "H" as "[H|H]".
        { iExFalso. iDestruct "H" as (βv) "[H _]".
          iRewrite "Hav" in "H". rewrite Hfa.
          iApply (option_equivI with "H"). }
        iDestruct "H" as "[_ H]".
        iMod ("H" with "Hs") as "H". iModIntro.
        iRewrite "Hav" in "H". done.
      + iDestruct "H" as "[Hav H]".
        iMod ("H" with "Hs") as "[Hsafe H]". iModIntro.
        iSplit.
        { (* safety *)
          iDestruct "Hsafe" as (α' σ') "Hsafe".
          iExists (f α'), σ'. iApply (istep_hom with "Hsafe") . }
        iIntros (σ' β) "Hst".
        rewrite {1}istep_hom_inv. iDestruct "Hst" as "[%Ha | [_ Hst]]".
        { destruct Ha as [αv ->]. iExFalso.
          iApply (option_equivI with "Hav"). }
        iDestruct "Hst" as (α') "[Hst Hb]".
        iMod ("H" with "Hst") as "H". iModIntro.
        iNext. iMod "H" as "H". iModIntro.
        iMod "H" as "H". iModIntro.
        iNext.
        iMod "H" as "H". iModIntro.
        iMod "H" as "[$ H]".
        iModIntro. iRewrite "Hb". by iApply "IH".
  Qed.

  Lemma wp_tick α E1 Φ :
    ▷ WP α @ E1 {{ Φ }} ⊢ WP (Tick α) @ E1 {{ Φ }}.
  Proof.
    iIntros "H". rewrite (wp_unfold _ (Tick _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Tau. }
    iIntros (σ) "Hs". iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl". iSplit.
    - iExists α,σ. iLeft. eauto.
    - iIntros (σ' β) "Hst". rewrite istep_tick.
      iDestruct "Hst" as "[Hb Hs']".
      iRewrite "Hs'" in "Hs". iFrame "Hs".
      iModIntro. iNext. iModIntro.
      iModIntro. iNext. iModIntro.
      iMod "Hcl" as "_".
      iModIntro. iRewrite "Hb". by iFrame.
  Qed.

  Lemma reify_vis_eq_int op i k o σ σ' :
    (gReifiers_re rs op (i,σ) ≡ Some (o,σ') ⊢@{iProp} reify (Vis op i k) σ ≡ (σ', Tau $ k o))%I.
  Proof. Admitted.

  Lemma wp_reify_idx E1 E2 Φ i (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid F := (existT i lop) in
    forall (x : Ins (F op) ♯ IT)
           (k : Outs (F op) ♯ IT  -n> laterO IT)  σ,
    has_state_idx i σ -∗
    (|={E1,E2}=> ∃ y σ' β,
                  sReifier_re (rs !!! i) lop (x, σ) ≡ Some (y, σ') ∗
                  k y ≡ Next β ∗
         ▷ ▷ |={E2,E1}=> (has_state_idx i σ' -∗ WP β @ E1 {{ Φ }}))
    -∗ WP (Vis op x k) @ E1 {{ Φ }}.
  Proof.
    intros op x k σ.
    iIntros "Hlst H".
    rewrite (wp_unfold _ (Vis _ _ _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Vis. }
    iIntros (fs) "Hgst".
    destruct (gState_decomp i fs) as [σ0 rest] eqn:Hdecomp.
    assert (fs ≡ gState_recomp rest σ0) as Hfs.
    { unfold gState_recomp. simpl.
      rewrite -Hdecomp. unfold gState_decomp.
      rewrite ofe_iso_21//. }
    Opaque gState_recomp.
    iAssert (σ0 ≡ σ)%I with "[Hlst Hgst]" as "#Hss".
    { admit. }
    iMod "H" as "H".
    iDestruct "H" as (y σ' β) "[Hreify [Hk H]]".
    iAssert (gReifiers_re rs op (x,fs) ≡ Some (y,gState_recomp rest σ'))%I
      with "[Hreify]"  as "Hgreify".
    { rewrite Hfs.
      rewrite gReifiers_re_idx.
      iRewrite "Hss". admit. }
    iPoseProof (@reify_vis_eq_int _ _ k with "Hgreify") as "Hreify".
    iRewrite "Hk" in "Hreify".
    rewrite -Tick_eq.
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl2".
    iSplit.
    { (* it is safe *)
      iExists β,(gState_recomp rest σ'). iRight. iExists op,x,k.
      eauto. }
    iIntros (σ0' α0) "Hst". rewrite istep_vis.
    iRewrite "Hss" in "Hst".
    iAssert (▷ (α0 ≡ β) ∧ σ0' ≡ σ')%I with "[Hreify Hst]" as "[Ha1 #Hss']".
    { iRewrite "Hreify" in "Hst".
      iPoseProof (prod_equivI with "Hst") as "[Ha Hs]". simpl.
      iSplit.
      + iNext. by iApply internal_eq_sym.
      + by iApply internal_eq_sym.  }
    iMod (state_interp_has_state_update σ' with "Hσ0 Hs") as "[Hs0' Hs']".
    iRewrite -"Hss'" in "Hs0'".
    iModIntro. iNext. iModIntro.
    iModIntro. iNext. iModIntro.
    iMod "Hcl2" as "_".
    iMod "H" as "H".
    iModIntro. iFrame "Hs0'".
    iRewrite "Ha1". by iApply "H".


    Check (gState_decomp_recomp i).
  Lemma wp_reify_annoying op i ko σ  Φ E1 E2 :
    has_state σ -∗
    (|={E1,E2}=> ∃ β σ', reify (Vis op i ko) σ ≡ (σ', Tick β) ∗
         ▷ ▷ |={E2,E1}=> (has_state σ' -∗ WP β @ E1 {{ Φ }}))
          -∗ WP (Vis op i ko) @ E1 {{ Φ }}.
  Proof.
    iIntros "Hs H".
    rewrite (wp_unfold _ (Vis _ _ _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Vis. }
    iIntros (σ0) "Hσ0".
    iPoseProof (state_interp_has_state_agree with "Hσ0 Hs") as "#Hss".
    iMod "H" as "H".
    iDestruct "H" as (β σ') "[Hreify H]".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl2".
    iSplit.
    { (* it is safe *)
      iExists β,σ'. iRight. iExists op,i,ko.
      iRewrite "Hss". eauto. }
    iIntros (σ0' α0) "Hst". rewrite istep_vis.
    iRewrite "Hss" in "Hst".
    iAssert (▷ (α0 ≡ β) ∧ σ0' ≡ σ')%I with "[Hreify Hst]" as "[Ha1 #Hss']".
    { iRewrite "Hreify" in "Hst".
      iPoseProof (prod_equivI with "Hst") as "[Ha Hs]". simpl.
      iSplit.
      + iNext. by iApply internal_eq_sym.
      + by iApply internal_eq_sym.  }
    iMod (state_interp_has_state_update σ' with "Hσ0 Hs") as "[Hs0' Hs']".
    iRewrite -"Hss'" in "Hs0'".
    iModIntro. iNext. iModIntro.
    iModIntro. iNext. iModIntro.
    iMod "Hcl2" as "_".
    iMod "H" as "H".
    iModIntro. iFrame "Hs0'".
    iRewrite "Ha1". by iApply "H".
  Qed.

  Lemma wp_reify op i ko β σ σ' Φ E1 :
    reify (Vis op i ko) σ ≡ (σ', Tick β) →
    has_state σ -∗ (has_state σ' -∗ ▷ WP β @ E1 {{ Φ }})
          -∗ WP (Vis op i ko) @ E1 {{ Φ }}.
  Proof.
    intros Hreify. iIntros "Hs Hb".
    rewrite (wp_unfold _ (Vis _ _ _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Vis. }
    iIntros (σ0) "Hσ0".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl".
    (* we know what the real state is *)
    iPoseProof (state_interp_has_state_agree with "Hσ0 Hs") as "#Hss".
    iSplit.
    { (* it is safe *)
      iExists β,σ'. iRight. iExists op,i,ko.
      iRewrite "Hss". eauto. }
    iIntros (σ0' α0) "Hst". rewrite istep_vis.
    iRewrite "Hss" in "Hst".
    iAssert (▷ (α0 ≡ β) ∧ σ0' ≡ σ')%I with "[Hst]" as "[Ha1 Hss']".
    { rewrite Hreify.
      iPoseProof (prod_equivI with "Hst") as "[Ha Hs]". simpl.
      iSplit.
      + iNext. by iApply internal_eq_sym.
      + by iApply internal_eq_sym.  }
    iMod (state_interp_has_state_update σ' with "Hσ0 Hs") as "[Hs0 Hs]".
    iRewrite -"Hss'" in "Hs0".
    iSpecialize ("Hb" with "Hs"). iFrame "Hs0".
    iModIntro. iNext. iModIntro.
    iModIntro. iNext. iModIntro.
    iMod "Hcl" as "_".
    iRewrite "Ha1". done.
  Qed.

  Lemma wp_subreify {F} {stateF} (op : opid F) (i : Ins (F op) ♯ IT)
    (re : reify_eff F stateF) `{!subReifier re rs rest}
    (ko : Outs (E (subEff_opid op)) ♯ IT -n> laterO IT)
    (o : Outs (F op) ♯ IT)
    (σ1 σ1' : stateF ♯ IT) (σr : rest ♯ IT) α Φ E1 :
    re op IT _ (i,σ1) ≡ Some (o,σ1') →
    ko (subEff_conv_outs o) ≡ Next α →
    has_state (subState_conv_state σr σ1) -∗ (has_state (subState_conv_state σr σ1')
          -∗ ▷ WP α @ E1 {{ Φ }}) -∗
       WP (Vis (subEff_opid op) (subEff_conv_ins i) ko) @ E1 {{ Φ }}.
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
    ={⊤,∅}=∗ |={∅}▷=>^2 |={∅,⊤}=> state_interp σ' ∗ WP β {{ Ψ }}.
  Proof.
    iIntros "Hstep Hs H".
    rewrite (wp_unfold _ α). iDestruct "H" as "[H|[Ha H]]".
    - iExFalso. iDestruct "H" as (αv) "[H _]".
      iApply (istep_ITV with "H Hstep").
    - iSpecialize ("H" with "Hs"). iDestruct "H" as "[_ H]".
      iSimpl.
      iMod "H" as "H". iModIntro.
      iSpecialize ("H" with "Hstep").
      done.
  Qed.

  Lemma wp_isteps k α σ β σ' Ψ :
    ⊢ isteps α σ β σ' k -∗ state_interp σ -∗ WP α {{ Ψ }}
    -∗ mega_fupdN k (state_interp σ' ∗ WP β {{ Ψ }}).
  Proof.
    iInduction k as [|k] "IH" forall (α σ).
    - rewrite isteps_0. iIntros "[Ha Hs]".
      simpl. iRewrite "Ha". iRewrite "Hs".
      eauto with iFrame.
    - rewrite isteps_S. iDestruct 1 as (α1 σ1) "[Hstep Hsts]".
      iIntros "Hst H". iSimpl.
      iPoseProof (wp_istep with "Hstep Hst H") as "H".
      iMod "H" as "H". iModIntro.
      iMod "H" as "H". iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "H". iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "[Hs H]". iModIntro.
      iApply ("IH" with "Hsts Hs H").
  Qed.

  Lemma wp_ssteps α σ β σ' k Ψ :
    ssteps α σ β σ' k →
    state_interp σ ∗ WP α {{ Ψ }}
      ⊢ mega_fupdN k (state_interp σ' ∗ WP β {{ Ψ }}).
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (isteps α σ β σ' k) as "Hst".
    { by iApply ssteps_isteps. }
    iApply (wp_isteps with "Hst Hs HIC").
  Qed.

  Lemma wp_ssteps_isafe α σ β σ' k Ψ :
    ssteps α σ β σ' k →
    state_interp σ ∗ WP α {{ Ψ }}
      ⊢ mega_fupdN k
        (⌜is_Some (IT_to_V β)⌝
           ∨ |={⊤,∅}=> ∃ β2 σ2, istep β σ' β2 σ2).
  Proof.
    intros Hst. rewrite wp_ssteps//.
    apply mega_fupdN_mono.
    iIntros "[Hst H]".
    rewrite wp_unfold. iDestruct "H" as "[H | [Hb H]]".
    - iLeft. iDestruct "H" as (av) "[H _]".
      destruct (IT_to_V β) as [βv|]; first by eauto.
      iExFalso. iApply (option_equivI with "H").
    - iRight. iMod ("H" with "Hst") as "[$ _]".
      done.
  Qed.

  Lemma wp_ssteps_val α σ βv σ' k Ψ `{!NonExpansive Ψ} :
    ssteps α σ (IT_of_V βv) σ' k →
    state_interp σ ∗ WP α {{ Ψ }}
                 ⊢ mega_fupdN k $ |={⊤}=> Ψ βv.
  Proof.
    intros Hst. rewrite wp_ssteps//.
    apply mega_fupdN_mono.
    iIntros "[Hst H]".
    rewrite wp_unfold. iDestruct "H" as "[H | [Hb H]]".
    - iDestruct "H" as (av) "[H HH]".
      rewrite IT_to_of_V. iPoseProof (option_equivI with "H") as "H".
      by iRewrite "H".
    - rewrite IT_to_of_V.
      iExFalso. iApply (option_equivI with "Hb").
  Qed.

End weakestpre.

Arguments wp {_} rs {_ _ _ _} α E Φ.
Arguments has_state {E} {_ _ _} σ.
Arguments stateG {E} rs Σ.
Arguments stateΣ {E} rs.

Notation "'WP@{' re } α {{ β , Φ } }" := (wp re α ⊤ (λ β, Φ))
    (at level 20, re, α, Φ at level 200,
     format "'WP@{' re }  α  {{  β ,  Φ  } }") : bi_scope.

Notation "'WP@{' re } α {{ Φ } }" := (wp re α ⊤ Φ)
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
  eapply (mega_fupdN_soundness_lc' _ (S k)).
  intros lc Hinv.
  rewrite -mega_fupdN_S_fupd. simpl.
  iMod (new_state_interp rs σ) as (sg) "[Hs Hs2]".
  destruct (Hprf lc Σ Hinv sg) as (Φ & HΦ & HΦψ & Hprf').
  iPoseProof (Hprf' with "Hs2") as "Hic".
  iPoseProof (wp_ssteps with "[$Hs $Hic]") as "Hphi".
  { eassumption. }
  iApply fupd_mask_intro; first solve_ndisj.
  iIntros "Hcl". iModIntro. iNext. iModIntro. iModIntro. iNext.
  iModIntro.
  iMod "Hcl" as "_". iModIntro.
  iApply (mega_fupdN_mono with "Hphi").
  rewrite bi.sep_elim_r. rewrite -HΦψ.
  rewrite wp_val_inv; eauto.
Qed.
