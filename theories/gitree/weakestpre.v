From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import base tactics classes modality_instances.
From iris.base_logic.lib Require Export own fancy_updates invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify greifiers reductions.

(** * Ghost state from gReifiers *)

Definition gReifiers_ucmra {n} {a : is_ctx_dep} (rs : gReifiers a n)
  (X : ofe) `{!Cofe X} : ucmra :=
  discrete_funUR (λ (i : fin n),
      optionUR (exclR (sReifier_state (rs !!! i) ♯ X))).

(** The resource corresponding to the whole global state *)
Definition of_state {n} {a : is_ctx_dep} (rs : gReifiers a n)
  (X : ofe) `{!Cofe X} (st : gReifiers_state rs ♯ X)
  : gReifiers_ucmra rs X :=
  λ i, Excl' (fstO (gState_decomp i st)).

(** The resource corresponding to a speicific projection out of the global state *)
Definition of_idx {n} {a : is_ctx_dep} (rs : gReifiers a n)
  (X : ofe) `{!Cofe X} (i : fin n)
  (st : sReifier_state (rs !!! i) ♯ X) : gReifiers_ucmra rs X.
Proof.
  simple refine (λ j, if (decide (j = i)) then _ else None).
  simpl. induction e. exact (Excl' st).
Defined.

Lemma of_state_recomp_lookup_ne {n} {a : is_ctx_dep} (rs : gReifiers a n)
  (X : ofe) `{!Cofe X}
  i j (σ1 σ2 : sReifier_state (rs !!! i) ♯ X) rest :
  i ≠ j →
  of_state rs X (gState_recomp rest σ1) j
    ≡ of_state rs X (gState_recomp rest σ2) j.
Proof.
  intros Hij. revert σ1 σ2 rest.
  unfold of_state.
  induction rs as [|n r rs'].
  { inversion i. }
  inv_fin i; simpl.
  { inv_fin j; first naive_solver.
    intros i s1 s2 rest H0.
    simpl. reflexivity. }
  inv_fin j.
  { intros i s1 s2 rest H0.
    simpl. reflexivity. }
  intros i j s1 s2 rest H0.
  simpl. apply IHrs'.
  intro. simplify_eq/=.
Qed.

Section ucmra.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n).
  Context (X : ofe) `{!Cofe X}.
  Notation gReifiers_ucmra := (gReifiers_ucmra rs X).
  Notation of_state := (of_state rs X).
  Notation of_idx := (of_idx rs X).

  #[export] Instance of_state_ne : NonExpansive of_state.
  Proof. solve_proper. Qed.
  #[export] Instance of_state_proper : Proper ((≡) ==> (≡)) of_state.
  Proof. apply ne_proper, _. Qed.

  Lemma of_state_valid (σ : gReifiers_state rs ♯ X) : ✓ (of_state σ).
  Proof. intro; done. Qed.

  Lemma of_state_recomp_lookup i (σ : sReifier_state (rs !!! i) ♯ X) rest :
    of_state (gState_recomp rest σ) i ≡ Excl' σ.
  Proof.
    unfold of_state.
    rewrite gState_decomp_recomp. done.
  Qed.
  Lemma of_state_decomp_local_update i (σ σ1 σ2 : sReifier_state (rs !!! i) ♯ X) rest :
    (of_state (gState_recomp rest σ1), of_idx i σ2)
      ~l~> (of_state (gState_recomp rest σ), of_idx i σ).
  Proof.
    apply discrete_fun_local_update.
    intros j.
    destruct (decide (j = i)) as [->|Hneq].
    - unfold of_idx.
      destruct decide as [Heq|Hneq]; last done.
      rewrite (eq_pi i i Heq eq_refl). simpl.
      rewrite !of_state_recomp_lookup.
      by apply option_local_update, exclusive_local_update.
    - unfold of_idx.
      destruct decide as [Heq|Hneq']; first done.
      rewrite of_state_recomp_lookup_ne//.
  Qed.

  Lemma of_state_of_idx_agree i σ1 σ2 rest f Σ :
    of_state (gState_recomp rest σ1) ≡ of_idx i σ2 ⋅ f ⊢@{iProp Σ} σ1 ≡ σ2.
  Proof.
    iIntros "Hs".
    rewrite discrete_fun_equivI.
    iSpecialize ("Hs" $! i).
    unfold of_state.
    rewrite gState_decomp_recomp.
    rewrite discrete_fun_lookup_op.
    unfold of_idx.
    simpl.
    destruct decide as [Heq|Hneq]; last done.
    rewrite (eq_pi i i Heq eq_refl). simpl.
    destruct (f i) as [fi|]; rewrite option_equivI/= excl_equivI/=//.
  Qed.

End ucmra.

Section weakestpre.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n) {A} `{!Cofe A}.
  Notation rG := (gReifiers_sReifier rs).
  Notation F := (sReifier_ops rG).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Let of_idx := (of_idx rs IT).
  Notation reify := (reify rG).
  Notation istep := (istep rG).
  Notation isteps := (isteps rG).
  Notation sstep := (sstep rG).
  Notation ssteps := (ssteps rG).

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
  Definition has_state_idx `{!stateG Σ}
    (i : fin n) (σ : sReifier_state (rs !!! i) ♯ IT) : iProp Σ :=
    (own stateG_name (◯ (of_idx i σ)))%I.
  Definition has_substate {sR : sReifier a} `{!stateG Σ} `{!subReifier sR rs}
    (σ : sReifier_state sR ♯ IT) : iProp Σ :=
    (own stateG_name (◯ (of_idx sR_idx (sR_state σ))))%I.

  #[export] Instance state_interp_ne `{!stateG Σ} : NonExpansive state_interp.
  Proof. solve_proper. Qed.
  #[export] Instance state_interp_proper `{!stateG Σ}
    : Proper ((≡) ==> (≡)) state_interp.
  Proof. solve_proper. Qed.

  Lemma new_state_interp σ `{!invGS_gen hlc Σ, !statePreG Σ} :
    (⊢ |==> ∃ `{!stateG Σ}, state_interp σ ∗ has_full_state σ : iProp Σ)%I.
  Proof.
    iMod (own_alloc ((● (of_state σ)) ⋅ (◯ (of_state σ)))) as (γ) "[H1 H2]".
    { apply auth_both_valid_2; eauto. apply of_state_valid. }
    pose (sg := {| stateG_inG := _; stateG_name := γ |}).
    iModIntro. iExists sg. by iFrame.
  Qed.

  Lemma state_interp_has_state_idx_agree (i : fin n)
    (σ1 σ2 : sReifier_state (rs !!! i) ♯ IT)
    (rest : gState_rest i rs ♯ IT) `{!stateG Σ} :
    state_interp (gState_recomp rest σ1) -∗ has_state_idx i σ2 -∗ σ1 ≡ σ2.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "Hs".
    rewrite auth_both_validI.
    iDestruct "Hs" as "[Hs _]".
    iDestruct "Hs" as (f) "Hs".
    iApply (of_state_of_idx_agree with "Hs").
  Qed.

  Lemma state_interp_has_state_idx_update (i : fin n)
    (σ σ1 σ2 : sReifier_state (rs !!! i) ♯ IT)
    (rest : gState_rest i rs ♯ IT) `{!stateG Σ} :
    state_interp (gState_recomp rest σ1) -∗ has_state_idx i σ2 ==∗
      state_interp (gState_recomp rest σ) ∗ has_state_idx i σ.
  Proof.
    iIntros "H1 H2".
    iMod (own_update_2 with "H1 H2") as "H".
    { apply auth_update.
      apply (of_state_decomp_local_update _ _ _ σ). }
    iDestruct "H" as "[$ $]". done.
  Qed.

  #[export] Instance subG_stateΣ {Σ} : subG stateΣ Σ → statePreG Σ.
  Proof. solve_inG. Qed.

  Context `{!invGS Σ} `{!stateG Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Definition stuckness := error → Prop.

  (** Weakest precondition *)
  Program Definition wp_pre (s : stuckness) (Φ : ITV → iProp)
     (self : coPsetO -n> IT -n> iProp)
    : coPsetO -n> IT -n> iProp
    := λne E α,
      ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E}=> Φ αv)
     ∨ (IT_to_V α ≡ None ∧ ∀ σ, state_interp σ ={E,∅}=∗
             ((∃ α' σ', istep α σ α' σ')
       ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))
           ∧ (∀ σ' β, istep α σ β σ' -∗ £ 1 ={∅}▷=∗ |={∅,E}=> state_interp σ' ∗ self E β)))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    intros ? ? ? ? E1 E2 ->.
    solve_proper.
  Qed.

  #[local] Instance wp_pre_contractive s Φ : Contractive (wp_pre s Φ).
  Proof.
    unfold wp_pre.
    intros m s1 s2 Hs E1 a'. simpl.
    (* repeat first [f_contractive | f_equiv; solve_proper *)
    (*   | f_equiv ]. *)
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_contractive. solve_proper.
    (* solve_contractive. *)
  Qed.
  Definition wp α s E Φ := fixpoint (wp_pre s Φ) E α.
  Lemma wp_unfold  α E' s Φ :
    wp α s E' Φ ≡
       ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E'}=> Φ αv)
     ∨ (IT_to_V α ≡ None ∧ ∀ σ, state_interp σ ={E',∅}=∗
             ((∃ α' σ', istep α σ α' σ')
                ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))
          ∧ (∀ σ' β, istep α σ β σ' -∗ £ 1 ={∅}▷=∗ |={∅,E'}=> state_interp σ' ∗ wp β s E' Φ)))%I.
  Proof. apply (fixpoint_unfold (wp_pre s Φ) _). Qed.

  Notation "'WP' α @ s ; E {{ Φ } }" := (wp α s E Φ)
    (at level 20, α, s, Φ at level 200, only parsing) : bi_scope.

  Notation "'WP' α @ s ; E {{ v , Q } }" := (wp α s E (λ v, Q))
    (at level 20, α, s, Q at level 200,
       format "'[hv' 'WP'  α  '/' @  s  ;  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  Notation "'WP' α @  s {{ β , Φ } }" := (wp α s ⊤ (λ β, Φ))
    (at level 20, α, Φ at level 200,
     format "'WP'  α  @  s  {{  β ,  Φ  } }") : bi_scope.

  Notation "'WP' α  @  s {{ Φ } }" := (wp α s ⊤ Φ)
    (at level 20, α, Φ at level 200,
     format "'WP'  α  @  s  {{  Φ  } }") : bi_scope.

  #[export] Instance wp_ne m :
    Proper ((dist m) ==>
              (pointwise_relation _ (iff)) ==>
              (dist m) ==> (pointwise_relation _ (dist m)) ==> (dist m)) wp.
  Proof.
    intros α1 α2 Ha s s' Hs E1 E2 HE Φ1 Φ2 Hp.
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
    f_equiv. f_equiv.
    f_contractive. f_equiv. f_equiv.
    f_equiv.
    apply IH; eauto. f_equiv.
    eapply dist_le; [apply Hp|lia].
  Qed.
  #[export] Instance wp_proper :
    Proper ((≡) ==> (pointwise_relation _ (iff)) ==> (≡) ==>
              (pointwise_relation _ (≡)) ==> (≡)) wp.
  Proof.
    intros α1 α2 Ha s s' Hs E1 E2 HE Φ1 Φ2 Hp.
    apply equiv_dist=>m.
    apply wp_ne; eauto.
    - intros v. by apply equiv_dist, Hp.
  Qed.

  Lemma wp_val' α αv s Φ E1 :
    IT_to_V α ≡ Some αv ⊢ (|={E1}=> Φ αv) -∗ WP α @ s ; E1 {{ Φ }}.
  Proof.
    iIntros "Ha Hp". rewrite wp_unfold. iLeft.
    iExists αv. by iFrame.
  Qed.
  Lemma wp_val α αv Φ s E1 `{!IntoVal α αv}:
    (|={E1}=> Φ αv) ⊢ WP α @ s ; E1 {{ Φ }}.
  Proof.
    iIntros "Hp". rewrite wp_unfold. iLeft.
    iExists αv. rewrite -IT_to_of_V into_val. by iFrame.
  Qed.

  Lemma wp_val_inv' α αv Φ `{!NonExpansive Φ} s E1 :
    IT_to_V α ≡ Some αv ⊢ WP α @ s ; E1 {{ Φ }} ={E1}=∗ Φ αv.
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

  Lemma wp_val_inv α αv Φ `{!NonExpansive Φ} s E1  `{!IntoVal α αv} :
    WP α @ s ; E1 {{ Φ }} ⊢ |={E1}=> Φ αv.
  Proof.
    iApply wp_val_inv'. iPureIntro.
    rewrite -IT_to_of_V into_val//.
  Qed.

  Lemma fupd_wp E1 α s Φ `{!NonExpansive Φ} :
    (|={E1}=> WP α @ s ; E1 {{ Φ }}) ⊢ WP α @ s ; E1 {{ Φ }}.
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
  #[export] Instance elim_modal_bupd_wp p E α P s Φ `{!NonExpansive Φ} :
    ElimModal True p false (|==> P) P (WP α @ s ; E {{ Φ }}) (WP α @ s ; E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    by rewrite (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  #[export] Instance elim_modal_fupd_wp p E α P s Φ `{!NonExpansive Φ} :
    ElimModal True p false (|={E}=> P) P (WP α @ s;E {{ Φ }}) (WP α @ s;E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Lemma wp_wand Ψ Φ α s E1 :
    (WP α @ s;E1 {{ Ψ }}) -∗ (∀ v, Ψ v ={E1}=∗ Φ v) -∗ WP α @ s;E1 {{ Φ }}.
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
      iModIntro. iIntros (σ' β) "Hst Hlc".
      iMod ("H" with "Hst Hlc") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "[$ H]".
      iModIntro. by iApply ("IH" with "H").
  Qed.

  Lemma wp_fupd E1 α s Φ : WP α @ s;E1 {{ v, |={E1}=> Φ v }} ⊢ WP α @ s;E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply (wp_wand with "H"); auto.
  Qed.

  (* XXX: strengthen it with later credits *)
  Lemma wp_tick α s E1 Φ :
    ▷ WP α @ s;E1 {{ Φ }} ⊢ WP (Tick α) @ s;E1 {{ Φ }}.
  Proof.
    iIntros "H". rewrite (wp_unfold (Tick _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Tau. }
    iIntros (σ) "Hs". iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl". iSplit.
    - iLeft. iExists α,σ. iLeft. eauto.
    - iIntros (σ' β) "Hst Hlc". rewrite istep_tick.
      iDestruct "Hst" as "[Hb Hs']".
      iRewrite "Hs'" in "Hs". iFrame "Hs".
      iModIntro. iNext. iModIntro.
      iMod "Hcl" as "_".
      iModIntro. iRewrite "Hb". by iFrame.
  Qed.

  Opaque gState_recomp.

  (* We can generalize this based on the stuckness bit *)
  Lemma wp_reify_idx E1 E2 s Φ i (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid F := (existT i lop) in
    forall (x : Ins (F op) ♯ IT)
           (k : Outs (F op) ♯ IT  -n> laterO IT),
    (|={E1,E2}=> ∃ σ σ' β, has_state_idx i σ ∗
                         ∀ rest, reify (Vis op x k) (gState_recomp rest σ)
                               ≡ (gState_recomp rest σ', Tick β) ∗
         ▷ (£ 1 -∗ has_state_idx i σ' -∗ |={E2,E1}=>  WP β @ s;E1 {{ Φ }}))
    -∗ WP (Vis op x k) @ s;E1 {{ Φ }}.
  Proof.
    intros op x k.
    iIntros "H".
    rewrite (wp_unfold (Vis _ _ _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Vis. }
    iIntros (fs) "Hgst".
    destruct (gState_decomp i fs) as [σ0 rest] eqn:Hdecomp.
    assert (fs ≡ gState_recomp rest σ0) as Hfs.
    { symmetry. apply gState_recomp_decomp.
      by rewrite Hdecomp. }
    iMod "H" as (σ σ' β) "[Hlst H]".
    iAssert (σ0 ≡ σ)%I with "[Hlst Hgst]" as "#Hss".
    { iEval (rewrite Hfs) in "Hgst".
      iApply (state_interp_has_state_idx_agree with "Hgst Hlst"). }
    iDestruct ("H" $! rest) as "[Hreify H]".
    iRewrite -"Hss" in "Hreify".
    iEval (rewrite -Hfs) in "Hreify".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl2".
    iSplit.
    { (* it is safe *)
      iLeft.
      iExists β, (gState_recomp rest σ'). iRight.
      iExists op, x, k; eauto. }
    iIntros (fs' α0) "Hst Hlc". rewrite istep_vis.
    iAssert (gState_recomp rest σ' ≡ fs' ∧ Tick β ≡ Tick α0)%I
      with "[Hreify Hst]" as "[Hst Hb]".
    { iRewrite "Hreify" in "Hst".
      by rewrite prod_equivI. }
    iEval (rewrite Hfs) in "Hgst".
    iMod (state_interp_has_state_idx_update i σ' with "Hgst Hlst") as "[Hgst Hlst]".
    iModIntro. iNext. iModIntro.
    iMod "Hcl2" as "_".
    iMod ("H" with "Hlc Hlst") as "H".
    iModIntro. iRewrite -"Hst".
    iRewrite -"Hb". by iFrame.
  Qed.

  Lemma wp_reify  E1 s Φ i (lop : opid (sReifier_ops (rs !!! i)))
    x k σ σ' β :
    let op : opid F := (existT i lop) in
    (∀ rest, reify (Vis op x k)  (gState_recomp rest σ) ≡ (gState_recomp rest σ', Tick β)) →
    has_state_idx i σ -∗
    ▷ (£ 1 -∗ has_state_idx i σ' -∗ WP β @ s;E1 {{ Φ }})
    -∗ WP (Vis op x k) @ s;E1 {{ Φ }}.
  Proof.
    intros op Hr.
    iIntros "Hlst H".
    iApply wp_reify_idx.
    iModIntro. iExists σ, σ', β.
    iFrame "Hlst". iIntros (rest).
    iSplitR.
    { rewrite (Hr rest)//. }
    iNext. iIntros "Hlc Hs".
    iModIntro. by iApply ("H" with "Hlc Hs").
  Qed.

  Lemma wp_err E1 e (s : error → Prop) Φ :
    s e →
    ⊢ WP (Err e) @ s;E1 {{ Φ }}.
  Proof.
    intros hse.
    rewrite wp_unfold.
    iRight. iSplit.
    { rewrite IT_to_V_Err//. }
    iIntros (σ) "Hσ". iApply fupd_mask_intro; first set_solver.
    iIntros "Hcl".
    iSplit.
    { iRight. eauto with iFrame. }
    iIntros (σ' β) "Hst". iExFalso.
    iApply istep_err. done.
  Qed.

  Lemma wp_stuckness_mono α E1 (s1 s2 : error → Prop) Φ :
    (∀ e, s1 e → s2 e) →
    WP α @ s1;E1 {{ Φ }} ⊢ WP α @ s2;E1 {{ Φ }}.
  Proof.
    intros hse. iIntros "H1".
    iLöb as "IH" forall (α).
    rewrite !wp_unfold.
    iDestruct "H1" as "[H1 | H1]".
    - iLeft. iDestruct "H1" as (av) "[H1 H]".
      iExists _. iSplit; eauto.
    - iRight. iDestruct "H1" as "[H1 H]".
      iSplit; first by eauto. iIntros (σ) "Hs".
      iMod ("H" with "Hs") as "[Hs H]".
      iModIntro. iSplit.
      { iDestruct "Hs" as "[$ | Hs]".
        iRight. iDestruct "Hs" as (e) "[He %]".
        iExists e; iSplit; eauto. }
      iIntros (σ' β) "Hst Hlc".
      iMod ("H" with "Hst Hlc") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "[$ H]".
      iModIntro. by iApply ("IH" with "H").
  Qed.

  (** "adequacy" statemnts *)
  Lemma wp_istep α σ β σ' s Ψ :
    ⊢ istep α σ β σ' -∗ state_interp σ -∗ WP α @ s {{ Ψ }} -∗
    £ 2 ={⊤}=∗ state_interp σ' ∗ WP β @ s {{ Ψ }}.
  Proof.
    iIntros "Hstep Hs H [Hlc Hlc']".
    rewrite (wp_unfold α). iDestruct "H" as "[H|[Ha H]]".
    - iExFalso. iDestruct "H" as (αv) "[H _]".
      iApply (istep_ITV with "H Hstep").
    - iSpecialize ("H" with "Hs"). iDestruct "H" as "[_ H]".
      iSimpl.
      iMod "H" as "H".
      iMod ("H" with "Hstep Hlc'") as "H".
      iApply (fupd_trans ∅ ∅).
      iApply (lc_fupd_elim_later with "Hlc").
      iNext.
      iMod "H" as "H".
      by iMod "H" as "H".
  Qed.

  Lemma wp_isteps k α σ β σ' s Ψ :
    ⊢ isteps α σ β σ' k -∗ state_interp σ -∗ WP α @ s {{ Ψ }}
    -∗ £ (3*k) ={⊤}=∗ (state_interp σ' ∗ WP β @ s {{ Ψ }}).
  Proof.
    iInduction k as [|k] "IH" forall (α σ).
    - rewrite isteps_0. iIntros "[Ha Hs]".
      simpl. iRewrite "Ha". iRewrite "Hs".
      eauto with iFrame.
    - rewrite isteps_S. iDestruct 1 as (α1 σ1) "[Hstep Hsts]".
      iIntros "Hst H Hlc". iSimpl.
      rewrite -mult_n_Sm. iDestruct "Hlc" as "[Hk [Hone Htwo]]".
      iPoseProof (wp_istep with "Hstep Hst H") as "H".
      iMod ("H" with "Htwo") as "[Hs H]".
      iApply (fupd_trans ⊤ ⊤).
      iApply (lc_fupd_elim_later with "Hone").
      iNext.
      iApply ("IH" with "Hsts Hs H Hk").
  Qed.

  Lemma wp_ssteps α σ β σ' k s Ψ :
    ssteps α σ β σ' k →
    state_interp σ ∗ WP α @ s {{ Ψ }}
      ⊢  £ (3*k) ={⊤}=∗ (state_interp σ' ∗ WP β @ s {{ Ψ }}).
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (isteps α σ β σ' k) as "Hst".
    { by iApply ssteps_isteps. }
    iApply (wp_isteps with "Hst Hs HIC").
  Qed.

  Lemma IT_error_lem α :
    ⊢@{iProp} (∃ e, α ≡ Err e) ∨ ¬ (∃ e, α ≡ Err e).
  Proof.
      destruct (IT_dont_confuse α)
        as [[e Ha] | [[m Ha] | [ [g Ha] | [[α' Ha]|[op [i [ko Ha]]]] ]]].
      + eauto.
      + iRight; setoid_rewrite Ha.
        iDestruct 1 as (e) "Ha".
        iApply (IT_ret_err_ne with "Ha").
      + iRight; setoid_rewrite Ha.
        iDestruct 1 as (e) "Ha".
        iApply (IT_fun_err_ne with "Ha").
      + iRight; setoid_rewrite Ha.
        iDestruct 1 as (e) "Ha".
        iApply (IT_tick_err_ne with "Ha").
      + iRight; setoid_rewrite Ha.
        iDestruct 1 as (e) "Ha".
        iApply (IT_vis_err_ne with "Ha").
  Qed.

  Lemma wp_ssteps_isafe α σ β σ' k s Ψ :
    ssteps α σ β σ' k →
    state_interp σ ∗ WP α @ s {{ Ψ }}
      ⊢  £ (3 * k + 2) ={⊤,∅}=∗
        (⌜is_Some (IT_to_V β)⌝
           ∨ (∃ β2 σ2, istep β σ' β2 σ2)
           ∨ (∃ e, β ≡ Err e ∧ ⌜s e⌝)).
  Proof.
    intros Hst. rewrite wp_ssteps//.
    iIntros "H [Hlc [Hone Htwo]]". iSpecialize ("H" with "Hlc").
    iMod "H" as "[Hs H]".
    rewrite wp_unfold. iDestruct "H" as "[H | [Hb H]]".
    - iLeft. iDestruct "H" as (av) "[H _]".
      iApply (fupd_mask_weaken ∅); first done.
      iIntros "_".
      iModIntro.
      destruct (IT_to_V β) as [βv|]; first by eauto.
      iExFalso. iApply (option_equivI with "H").
    - iPoseProof (IT_error_lem β) as "Heq".
      iDestruct "Heq" as "[Heq|Heq]".
      + iDestruct "Heq" as (e) "Heq".
        iRight. iRight.
        iSpecialize ("H" with "Hs").
        iMod ("H") as "[#Hst H]".
        iDestruct "Hst" as "[Hst|Hst]".
        { iExFalso. iDestruct "Hst" as (α' σ'0) "Hst".
          iRewrite "Heq" in "Hst".
          iApply (istep_err with "Hst"). }
        iModIntro. done.
      + iRight. iLeft.
        iMod ("H" with "Hs") as "[#Hst H]".
        iDestruct "Hst" as "[Hst|Hst]"; last first.
        { iExFalso. iDestruct "Hst" as (e') "[Hst ?]".
          iApply "Heq". eauto with iFrame. }
        iFrame "Hst".
        iDestruct "Hst" as (? ?) "Hst".
        iSpecialize ("H" with "Hst Hone").
        iApply (fupd_trans ∅ ∅).
        iMod "H" as "H".
        iApply (lc_fupd_elim_later with "Htwo").
        iNext.
        iMod "H" as "H".
        iMod "H" as "H".
        iApply (fupd_mask_weaken ∅); first done.
        iIntros "_".
        iModIntro. done.
  Qed.

  Lemma wp_ssteps_val α σ βv σ' k s Ψ `{!NonExpansive Ψ} :
    ssteps α σ (IT_of_V βv) σ' k →
    state_interp σ ∗ WP α @ s {{ Ψ }}
                 ⊢ £ (3*k) ={⊤}=∗ Ψ βv.
  Proof.
    intros Hst. rewrite wp_ssteps//.
    iIntros "H Hk". iSpecialize ("H" with "Hk").
    iMod "H" as "[Hs H]".
    rewrite wp_unfold. iDestruct "H" as "[H | [Hb H]]".
    - iDestruct "H" as (av) "[H HH]".
      rewrite IT_to_of_V. iPoseProof (option_equivI with "H") as "H".
      by iRewrite "H".
    - rewrite IT_to_of_V.
      iExFalso. iApply (option_equivI with "Hb").
  Qed.

  Global Instance upd_ne {X : ofe} E (Φ : X -n> iProp) :
    NonExpansive (λ (a : X), (|={E}=> Φ a)%I).
  Proof.
    solve_proper.
  Qed.

  Global Instance upd_ast_l {X : ofe} R (Φ : X -n> iProp) :
    NonExpansive (λ (a : X), (R ∗ Φ a)%I).
  Proof.
    solve_proper.
  Qed.

  Global Instance upd_ast_r {X : ofe} R (Φ : X -n> iProp) :
    NonExpansive (λ (a : X), (Φ a ∗ R)%I).
  Proof.
    solve_proper.
  Qed.

End weakestpre.

Section weakestpre_specific.
  Context {n : nat} {A} `{!Cofe A}.

  Notation rG rs := (gReifiers_sReifier (n := n) rs).
  Notation F rs := (sReifier_ops (rG rs)).
  Notation IT rs := (IT (F rs) A).
  Notation ITV rs := (ITV (F rs) A).
  Notation stateF rs := (gReifiers_state rs).
  Notation stateO rs := (stateF rs ♯ IT rs).
  Notation stateR rs := (gReifiers_ucmra rs (IT rs)).
  Let of_state {a} rs := (of_state (a:=a) rs (IT rs)).
  Let of_idx {a} rs := (of_idx (a:=a) rs (IT rs)).
  Notation reify rs := (reify (rG rs)).
  Notation istep rs := (istep (rG rs)).
  Notation isteps rs := (isteps (rG rs)).
  Notation sstep rs := (sstep (rG rs)).
  Notation ssteps rs := (ssteps (rG rs)).

  Context `{!invGS Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Lemma wp_reify_idx_ctx_dep (rs : gReifiers CtxDep n)
    `{!@stateG _ CtxDep rs A _ Σ} E1 E2 s Φ i
    (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid (F rs) := (existT i lop) in
    forall (x : Ins (F rs op) ♯ IT rs)
           (k : Outs (F rs op) ♯ IT rs -n> laterO (IT rs)),
    (|={E1,E2}=>
       ∃ σ y σ' β, has_state_idx rs i σ
                   ∗ sReifier_re (rs !!! i) lop (x, σ, k) ≡ Some (y, σ')
                   ∗ y ≡ Next β
                   ∗ ▷ (£ 1 -∗ has_state_idx rs i σ' ={E2,E1}=∗ wp rs β s E1 Φ))
    -∗ wp rs (Vis op x k) s E1 Φ.
  Proof.
    intros op x k.
    iIntros "H".
    iApply wp_reify_idx.
    iMod "H" as (σ y σ' β) "[Hlst [Hreify [Hk H]]]".
    iModIntro. iExists σ, σ', β.
    iFrame "Hlst".
    iIntros (rest).
    iFrame "H".
    iAssert (gReifiers_re rs _ _ op (x, gState_recomp rest σ, _)
               ≡ Some (y, gState_recomp rest σ'))%I
      with "[Hreify]"  as "Hgreify".
    { rewrite (@gReifiers_re_idx _ CtxDep).
      iAssert (optionO_map (prodO_map idfun (gState_recomp rest))
                 (sReifier_re (rs !!! i) lop (x, σ, k))
                 ≡ optionO_map (prodO_map idfun (gState_recomp rest))
                 (Some (y, σ')))%I with "[Hreify]" as "H".
      - iApply (f_equivI with "Hreify").
      - simpl. iExact "H".
    }
    iPoseProof (reify_vis_eqI_ctx_dep _ _ _ k with "Hgreify") as "Hreify".
    iRewrite "Hk" in "Hreify".
    by rewrite -Tick_eq.
  Qed.

  Lemma wp_reify_idx_ctx_indep (rs : gReifiers NotCtxDep n)
    `{!@stateG _ NotCtxDep rs A _ Σ} E1 E2 s Φ i
    (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid (F rs) := (existT i lop) in
    forall (x : Ins (F rs op) ♯ IT rs)
      (k : Outs (F rs op) ♯ IT rs -n> laterO (IT rs)),
    (|={E1,E2}=>  ∃ σ y σ' β, has_state_idx rs i σ
                             ∗ sReifier_re (rs !!! i) lop (x, σ) ≡ Some (y, σ')
                             ∗ k y ≡ Next β
                             ∗ ▷ (£ 1 -∗ has_state_idx rs i σ' ={E2,E1}=∗ wp rs β s E1 Φ))
    -∗ wp rs (Vis op x k) s E1 Φ.
  Proof.
    intros op x k.
    iIntros "H".
    iApply wp_reify_idx.
    iMod "H" as (σ y σ' β) "[Hlst [Hreify [Hk H]]]".
    iModIntro. iExists σ, σ', β.
    iFrame "Hlst".
    iIntros (rest).
    iFrame "H".
    iAssert (@gReifiers_re _ NotCtxDep rs _ _ op (x, gState_recomp rest σ)
               ≡ Some (y, gState_recomp rest σ'))%I
      with "[Hreify]"  as "Hgreify".
    { pose proof (@gReifiers_re_idx n NotCtxDep i rs (IT rs)) as J.
      simpl in J.
      simpl.
      rewrite J; clear J.
      iAssert (optionO_map (prodO_map idfun (gState_recomp rest))
                 (sReifier_re (rs !!! i) lop (x, σ))
                 ≡ optionO_map (prodO_map idfun (gState_recomp rest))
                 (Some (y, σ')))%I with "[Hreify]" as "H".
      - iApply (f_equivI with "Hreify").
      - simpl. iExact "H".
    }
    iPoseProof (reify_vis_eqI_ctx_indep _ _ _ k with "Hgreify") as "Hreify".
    iRewrite "Hk" in "Hreify".
    by rewrite -Tick_eq.
  Qed.

  Lemma wp_subreify_ctx_dep' (rs : gReifiers CtxDep n)
    `{!@stateG _ CtxDep rs A _ Σ} E1 E2 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR)) (x : Ins (sReifier_ops sR op) ♯ (IT rs))
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs)) :
    (|={E1,E2}=> ∃ σ y σ' β, has_substate rs σ ∗
                              sReifier_re sR op (x, σ, (k ◎ subEff_outs)) ≡ Some (y, σ')
                            ∗ y ≡ Next β
                            ∗ ▷ (£ 1 -∗ has_substate rs σ' ={E2,E1}=∗ wp rs β s E1 Φ))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    iIntros "H".
    iApply wp_reify_idx_ctx_dep.
    iMod "H" as (σ y σ' β) "[Hlst [Hreify [Hk H]]]".
    iModIntro.
    iExists (sR_state σ), y, (sR_state σ'), β.
    simpl.
    iFrame "Hlst H".
    rewrite subReifier_reify_idxI_ctx_dep.
    iFrame "Hk".
    iRewrite - "Hreify".
    iPureIntro.
    do 2 f_equiv.
    intros ?; simpl.
    by rewrite ofe_iso_12.
  Qed.

  Lemma wp_subreify_ctx_indep' (rs : gReifiers NotCtxDep n)
    `{!@stateG _ NotCtxDep rs A _ Σ} E1 E2 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR)) (x : Ins (sReifier_ops sR op) ♯ (IT rs))
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs)) :
    (|={E1,E2}=> ∃ σ y σ' β, has_substate rs σ ∗
                              sReifier_re sR op (x, σ) ≡ Some (y, σ')
                            ∗ k (subEff_outs y) ≡ Next β
                            ∗ ▷ (£ 1 -∗ has_substate rs σ' ={E2,E1}=∗ wp rs β s E1 Φ))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    iIntros "H".
    iApply wp_reify_idx_ctx_indep.
    iMod "H" as (σ y σ' β) "[Hlst [Hreify [Hk H]]]".
    iModIntro.
    iExists (sR_state σ),(subEff_outs y), (sR_state σ'), β.
    iFrame "Hlst H Hk".
    by iApply subReifier_reify_idxI_ctx_indep.
  Qed.

  Lemma wp_subreify_ctx_dep (rs : gReifiers CtxDep n)
    `{!@stateG _ CtxDep rs A _ Σ} E1 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs) (y : laterO (IT rs))
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β :
    sReifier_re sR op (x, σ, (k ◎ subEff_outs)) ≡ Some (y, σ') →
    y ≡ Next β →
    has_substate rs σ -∗
                      ▷ (£ 1 -∗ has_substate rs σ' -∗ wp rs β s E1 Φ)
    -∗
       wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    intros HSR Hk.
    iIntros "Hlst H".
    iApply (wp_reify with "Hlst H").
    intros rest.
    rewrite Tick_eq. rewrite -Hk.
    rewrite reify_vis_eq_ctx_dep //.
    pose proof (@subReifier_reify n CtxDep sR rs _
                  (IT rs) _ op x y (k ◎ subEff_outs) σ σ' rest) as H'.
    simpl in H'.
    rewrite <-H'.
    - simpl.
      repeat f_equiv.
      + intros ???.
        solve_proper.
      + intros ?; simpl.
        rewrite ofe_iso_12.
        reflexivity.
    - rewrite HSR.
      reflexivity.
  Qed.

  Lemma wp_subreify_ctx_indep (rs : gReifiers NotCtxDep n)
    `{!@stateG _ NotCtxDep rs A _ Σ} E1 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs)
    (y : Outs (sReifier_ops sR op) ♯ IT rs)
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β :
    sReifier_re sR op (x, σ) ≡ Some (y, σ') →
    k (subEff_outs y) ≡ Next β →
    has_substate rs σ -∗
                                ▷ (£ 1 -∗ has_substate rs σ' -∗ wp rs β s E1 Φ)
    -∗
       wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    intros HSR Hk.
    iIntros "Hlst H".
    iApply (wp_reify with "Hlst H").
    intros rest.
    rewrite Tick_eq. rewrite -Hk.
    rewrite reify_vis_eq_ctx_indep //.
    by apply (subReifier_reify (a := NotCtxDep)).
  Qed.

End weakestpre_specific.

Section weakestpre_bind.
  Context {n : nat} (rs : gReifiers NotCtxDep n) {A} `{!Cofe A}.
  Notation rG := (gReifiers_sReifier rs).
  Notation F := (sReifier_ops rG).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Let of_idx := (of_idx rs IT).
  Notation reify := (reify rG).
  Notation istep := (istep rG).
  Notation isteps := (isteps rG).
  Notation sstep := (sstep rG).
  Notation ssteps := (ssteps rG).
  Notation wp := (wp rs).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!invGS Σ} `{!stateG rs (A:=A) Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Notation "'WP' α @ s ; E {{ Φ } }" := (wp α s E Φ)
    (at level 20, α, s, Φ at level 200, only parsing) : bi_scope.

  Notation "'WP' α @ s ; E {{ v , Q } }" := (wp α s E (λ v, Q))
    (at level 20, α, s, Q at level 200,
       format "'[hv' 'WP'  α  '/' @  s  ;  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

  Lemma wp_bind (f : IT → IT) `{!IT_hom f} (α : IT) s Φ `{!NonExpansive Φ} E1 :
    WP α @ s;E1 {{ βv, WP (f (IT_of_V βv)) @ s;E1 {{ βv, Φ βv }} }} ⊢ WP (f α) @ s;E1 {{ Φ }}.
  Proof.
    assert (NonExpansive (λ βv0, WP f (IT_of_V βv0) @ s;E1 {{ βv1, Φ βv1 }})%I).
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
          iDestruct "Hsafe" as "[Hsafe|Herr]".
          - iDestruct "Hsafe" as (α' σ') "Hsafe". iLeft.
            iExists (f α'), σ'. iApply (istep_hom with "Hsafe").
          - iDestruct "Herr" as (e) "[Herr %]".
            iRight. iExists e. iSplit; last done.
            iRewrite "Herr". rewrite hom_err//. }
        iIntros (σ' β) "Hst".
        rewrite {1}istep_hom_inv. iDestruct "Hst" as "[%Ha | [_ Hst]]".
        { destruct Ha as [αv Ha]. rewrite Ha.
          iExFalso.
          iApply (option_equivI with "Hav"). }
        iDestruct "Hst" as (α') "[Hst Hb]".
        iIntros "Hlc".
        iMod ("H" with "Hst Hlc") as "H". iModIntro.
        iNext. iMod "H" as "H". iModIntro.
        iMod "H" as "[$ H]".
        iModIntro. iRewrite "Hb". by iApply "IH".
  Qed.

End weakestpre_bind.

Arguments wp {_ _} rs {_ _ _ _ _} α s E Φ.
Arguments has_full_state {n _ _ _ _ _ _} σ.
Arguments has_state_idx {n _ _ _ _ _ _} i σ.
Arguments has_substate {n _ _ _ _ _ _ _ _} σ.
Arguments stateG {n _} rs A {_} Σ.
Arguments statePreG {n _} rs A {_} Σ.
Arguments stateΣ {n _} rs A {_}.

Definition notStuck : stuckness := λ e, False.

Notation "'WP@{' re } α @ s ; E {{ Φ } }" :=
  (wp re α s E Φ)
    (at level 20, α, s, Φ at level 200, only parsing) : bi_scope.

Notation "'WP@{' re } α @ s ; E {{ v , Q } }" :=
  (wp re α s E (λ v, Q))
    (at level 20, α, s, Q at level 200,
      format "'[hv' 'WP@{' re }  α  '/' @  s  ;  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'WP@{' re } α @  s {{ β , Φ } }" :=
  (wp re α s ⊤ (λ β, Φ))
    (at level 20, α, Φ at level 200,
      format "'WP@{' re }  α  @  s  {{  β ,  Φ  } }") : bi_scope.

Notation "'WP@{' re } α  @  s {{ Φ } }" :=
  (wp re α s ⊤ Φ)
    (at level 20, α, Φ at level 200,
      format "'WP@{' re }  α  @  s  {{  Φ  } }") : bi_scope.

Notation "'WP@{' re } α {{ β , Φ } }" :=
  (wp re α notStuck ⊤ (λ β, Φ))
    (at level 20, α, Φ at level 200,
      format "'WP@{' re }  α  {{  β ,  Φ  } }") : bi_scope.

Notation "'WP@{' re } α {{ Φ } }" :=
  (wp re α notStuck ⊤ Φ)
    (at level 20, α, Φ at level 200,
      format "'WP@{' re }  α  {{  Φ  } }") : bi_scope.

Lemma wp_adequacy cr Σ `{!invGpreS Σ} n a (rs : gReifiers a n)
  {A} `{!Cofe A} `{!statePreG rs A Σ}
  (α : IT _ A) σ βv σ' s k (ψ : (ITV (gReifiers_ops rs) A) → Prop) :
  ssteps (gReifiers_sReifier rs) α σ (IT_of_V βv) σ' k →
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs A Σ},
     ∃ Φ, NonExpansive Φ ∧ (∀ βv, Φ βv ⊢ ⌜ψ βv⌝)
          ∧ (£ cr ∗ has_full_state σ ⊢ WP@{rs} α @ s {{ Φ }})%I)  →
  ψ βv.
Proof.
  intros Hst Hprf.
  cut (⊢ ⌜ψ βv⌝ : iProp Σ)%I.
  { intros HH. eapply uPred.pure_soundness; eauto. }
  eapply (step_fupdN_soundness_lc _ 0 (cr + 3*k)).
  intros Hinv. iIntros "[Hcr Hlc]".
  iMod (new_state_interp rs σ) as (sg) "[Hs Hs2]".
  destruct (Hprf Hinv sg) as (Φ & HΦ & HΦψ & Hprf').
  iPoseProof (Hprf' with "[$Hcr $Hs2]") as "Hic".
  iPoseProof (wp_ssteps with "[$Hs $Hic]") as "Hphi".
  { eassumption. }
  iMod ("Hphi" with "Hlc") as "[Hst H]".
  rewrite wp_val_inv; eauto.
  iMod "H" as "H".
  rewrite HΦψ. iFrame "H".
  by iApply fupd_mask_intro_discard.
Qed.

Lemma wp_safety cr Σ `{!invGpreS Σ} n a (rs : gReifiers a n)
  {A} `{!Cofe A} `{!statePreG rs A Σ} s k
  (α β : IT (gReifiers_ops rs) A) (σ σ' : gReifiers_state rs ♯ IT (gReifiers_ops rs) A) :
  (∀ Σ P Q, @disjunction_property Σ P Q) →
  ssteps (gReifiers_sReifier rs) α σ β σ' k →
  IT_to_V β ≡ None →
  (∀ `{H1 : !invGS_gen HasLc Σ} `{H2: !stateG rs A Σ},
     ∃ Φ, NonExpansive Φ ∧ (£ cr ∗ has_full_state σ ⊢ WP@{rs} α @ s {{ Φ }})%I)  →
  ((∃ β1 σ1, sstep (gReifiers_sReifier rs) β σ' β1 σ1)
   ∨ (∃ e, β ≡ Err e ∧ s e)).
Proof.
  Opaque istep.
  intros Hdisj Hstep Hbv Hwp.
  cut (⊢@{iProp Σ} (∃ β1 σ1, istep (gReifiers_sReifier rs) β σ' β1 σ1)
        ∨ (∃ e, β ≡ Err e ∧ ⌜s e⌝))%I.
  { intros [Hprf | Hprf]%Hdisj.
    - left.
      apply (istep_safe_sstep _ (Σ:=Σ)).
      { apply Hdisj. }
      done.
    - right.
      destruct (IT_dont_confuse β)
        as [[e Ha] | [[m Ha] | [ [g Ha] | [[α' Ha]|[op [i [ko Ha]]]] ]]].
      + exists e. split; eauto.
        eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (e') "[He %Hs]". rewrite Ha.
        iPoseProof (Err_inj' with "He") as "%He".
        iPureIntro. rewrite He//.
      + exfalso. eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (e') "[Ha Hs]". rewrite Ha.
        iApply (IT_ret_err_ne with "Ha").
      + exfalso. eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (e') "[Ha Hs]". rewrite Ha.
        iApply (IT_fun_err_ne with "Ha").
      + exfalso. eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (e') "[Ha Hs]". rewrite Ha.
        iApply (IT_tick_err_ne with "Ha").
      + exfalso. eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (e') "[Ha Hs]". rewrite Ha.
        iApply (IT_vis_err_ne with "Ha"). }
  eapply (step_fupdN_soundness_lc _ 0 (cr + (3*k+2))).
  intros Hinv. iIntros "[Hcr Hlc]".
  iMod (new_state_interp rs σ) as (sg) "[Hs Hs2]".
  destruct (Hwp Hinv sg) as (Φ & HΦ & Hprf').
  iPoseProof (Hprf' with "[$Hs2 $Hcr]") as "Hic".
  iPoseProof (wp_ssteps_isafe with "[$Hs $Hic]") as "H".
  { eassumption. }
  iMod ("H" with "Hlc") as "[H | H]".
  { iDestruct "H" as (βv) "%Hbeta".
    exfalso. rewrite Hbeta  in Hbv.
    inversion Hbv. }
  iFrame "H".
  by iApply fupd_mask_intro_discard.
Qed.
