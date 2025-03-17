From iris.algebra Require Import list.
From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import base tactics classes modality_instances.
From iris.base_logic.lib Require Export own fancy_updates invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify greifiers reductions.

Lemma cons_internal_equiv_tail {PROP : bi} `{!BiInternalEq PROP}
  {X : ofe} `{!Cofe X}
  (x y : listO X) a b :
  ⊢@{PROP} a :: x ≡ b :: y
   -∗ x ≡ y.
Proof.
  iIntros "H".
  by iApply (f_equivI tail (a :: x) (b :: y)).
Qed.

Lemma cons_internal_equiv_head {PROP : bi} `{!BiInternalEq PROP}
  {X : ofe} `{!Cofe X}
  (x y : listO X) a b :
  ⊢@{PROP} a :: x ≡ b :: y
   -∗ a ≡ b.
Proof.
  iIntros "H".
  iDestruct (f_equivI head (a :: x) (b :: y) with "H") as "G".
  simpl.
  by rewrite option_equivI.
Qed.

Lemma app_internal_equiv_app {PROP : bi} `{!BiInternalEq PROP}
  {X : ofe} `{!Cofe X}
  (x1 x2 y1 y2 : listO X) :
  ⊢@{PROP} x1 ++ x2 ≡ y1 ++ y2
    -∗ ∃ (l : listO X), x1 ≡ y1 ++ l
                        ∧ y2 ≡ l ++ x2 ∨ y1 ≡ x1 ++ l ∧ x2 ≡ l ++ y2.
Proof.
  iRevert (y1). iInduction x1 as [| a x1] "IH".
  - cbn. iIntros (y1) "Heq".
    iApply (internal_eq_rewrite (PROP := PROP) (y1 ++ y2) x2
                           (λ z,
                             ∃ l : listO X,
                               [] ≡ y1 ++ l ∧
                                 y2 ≡ l ++ z ∨ y1 ≡ l
                                               ∧ z ≡ l ++ y2)%I with "[Heq]").
    { solve_proper. }
    { by iApply internal_eq_sym. }
    iExists y1.
    by iRight.
  - iIntros ([| b y1]); cbn.
    + iIntros "Heq"; iRewrite - "Heq".
      iExists (a :: x1).
      by iLeft.
    + iIntros "#Heq".
      iDestruct (cons_internal_equiv_tail with "Heq") as "Heq'".
      iDestruct (cons_internal_equiv_head with "Heq") as "Heq''".
      iRewrite "Heq''".
      iDestruct ("IH" $! y1 with "Heq'") as (l) "[[G1 G2] | [G1 G2]]".
      * iRewrite "G1".
        iRewrite "G2".
        iExists l.
        iLeft; by iSplit.
      * iRewrite "G1".
        iRewrite "G2".
        iExists l.
        iRight; by iSplit.
Qed.

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
  Notation internal_step := (internal_step rG).
  Notation internal_steps := (internal_steps rG).
  Notation tp_internal_step := (tp_internal_step rG).
  Notation tp_internal_steps := (tp_internal_steps rG).
  Notation external_step := (external_step rG).
  Notation external_steps := (external_steps rG).
  Notation tp_external_step := (tp_external_step rG).
  Notation tp_external_steps := (tp_external_steps rG).

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
  #[export] Instance has_substate_ne {sR : sReifier a} `{!stateG Σ}
    `{!subReifier sR rs} : NonExpansive (has_substate).
  Proof.
    intros ????.
    unfold has_substate.
    do 2 f_equiv.
    intros i.
    unfold of_idx, weakestpre.of_idx.
    destruct (decide (i = sR_idx)).
    - subst; simpl.
      now do 3 f_equiv.
    - reflexivity.
  Qed.
  #[export] Instance has_substate_proper {sR : sReifier a} `{!stateG Σ}
    `{!subReifier sR rs} : Proper ((≡) ==> (≡)) (has_substate).
  Proof.
    intros ???.
    unfold has_substate.
    do 2 f_equiv.
    intros i.
    unfold of_idx, weakestpre.of_idx.
    destruct (decide (i = sR_idx)).
    - subst; simpl.
      now do 3 f_equiv.
    - reflexivity.
  Qed.

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
  Program Definition wp_pre (s : stuckness)
     (self : (ITV -d> iProp) -n> coPsetO -n> IT -n> iProp)
    : (ITV -d> iProp) -n> coPsetO -n> IT -n> iProp
    := λne Φ E α,
      ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E}=> Φ αv)
       ∨ (IT_to_V α ≡ None ∧ ∀ σ,
            state_interp σ
            ={E,∅}=∗ ((∃ α' σ' en, internal_step α σ α' σ' en)
                      ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))
            ∧ (∀ σ' β en, internal_step α σ β σ' en
                          -∗ £ 1
                          ={∅}▷=∗ |={∅,E}=>
                 state_interp σ'
                 ∗ self Φ E β
                 ∗ [∗ list] i ↦ ef ∈ en, self (λne _, True) ⊤ ef)))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. intros ?????? [] ?; simpl; solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  #[local] Instance wp_pre_contractive s : Contractive (wp_pre s).
  Proof.
    unfold wp_pre.
    intros m s1 s2 Hs Φ1 E1 a'. simpl.
    solve_contractive.
  Qed.

  Definition wp α s E Φ := fixpoint (wp_pre s) Φ E α.

  Lemma wp_unfold  α E' s Φ :
    wp α s E' Φ ≡
       ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E'}=> Φ αv)
        ∨ (IT_to_V α ≡ None
           ∧ ∀ σ, state_interp σ
                  ={E',∅}=∗ ((∃ α' σ' en, internal_step α σ α' σ' en)
                             ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))
                  ∧ (∀ σ' β en, internal_step α σ β σ' en
                                -∗ £ 1
                                ={∅}▷=∗ |={∅,E'}=>
                       state_interp σ'
                       ∗ wp β s E' Φ
                       ∗ [∗ list] i ↦ ef ∈ en, wp ef s ⊤ (λne _, True))))%I.
  Proof.
    rewrite /wp (fixpoint_unfold (wp_pre s) Φ E' α) //.
  Qed.

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
              (dist m) ==> (dist m) ==> (dist m)) wp.
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
    f_equiv; intros ?.
    f_equiv; first solve_proper. simpl.
    f_equiv. f_equiv.
    f_contractive. f_equiv. f_equiv.
    f_equiv.
    f_equiv.
    - apply IH; eauto.
      eapply dist_le; [apply Hp|lia].
    - do 3 f_equiv.
      unfold wp.
      do 3 f_equiv.
      apply fixpoint_ne.
      solve_proper.
  Qed.

  #[export] Instance wp_proper :
    Proper ((≡) ==> (pointwise_relation _ (iff)) ==> (≡) ==>
              (≡) ==> (≡)) wp.
  Proof.
    intros α1 α2 Ha s s' Hs E1 E2 HE Φ1 Φ2 Hp.
    apply equiv_dist=>m.
    apply wp_ne; eauto.
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
      iModIntro. iIntros (σ' β en) "Hst Hlc".
      iMod ("H" with "Hst Hlc") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "[$ [H G]]".
      iModIntro.
      iSplitL "H H2".
      + by iApply ("IH" with "H").
      + iFrame.
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
    - iLeft. iExists α,σ,[]. iLeft. eauto.
    - iIntros (σ' β en) "Hst Hlc". rewrite internal_step_tick.
      iDestruct "Hst" as "[Hb [Hs' Hen]]".
      iRewrite "Hs'" in "Hs". iFrame "Hs".
      iModIntro. iNext. iModIntro.
      iMod "Hcl" as "_".
      iModIntro. iRewrite "Hb".
      iFrame "H".
      destruct en.
      + done.
      + iExFalso.
        iPoseProof (list_equivI with "Hen") as "Hen".
        iSpecialize ("Hen" $! 0).
        by iPoseProof (option_equivI with "Hen") as "Hen".
  Qed.

  Lemma wp_tick_n α s E1 Φ k :
    ▷^k WP α @ s;E1 {{ Φ }} ⊢ WP (Tick_n k α) @ s;E1 {{ Φ }}.
  Proof.
    induction k as [| ? IHk]; first done.
    iIntros "H".
    iApply wp_tick.
    iNext.
    by iApply IHk.
  Qed.

  Opaque gState_recomp.

  (* We can generalize this based on the stuckness bit *)
  Lemma wp_reify_idx E1 E2 s Φ i (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid F := (existT i lop) in
    forall (x : Ins (F op) ♯ IT)
           (k : Outs (F op) ♯ IT  -n> laterO IT),
    (|={E1,E2}=> ∃ σ σ' β en,
       has_state_idx i σ ∗
         ∀ rest, reify (Vis op x k) (gState_recomp rest σ)
                   ≡ (gState_recomp rest σ', Tick β, en) ∗
                   ▷ (£ 1 -∗ has_state_idx i σ'
                      -∗ |={E2,E1}=>
                        WP β @ s;E1 {{ Φ }}
                                 ∗ [∗ list] i ↦ ef ∈ en, WP ef @ s; ⊤ {{ _, True }}))
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
    iMod "H" as (σ σ' β en) "[Hlst H]".
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
      iExists β, (gState_recomp rest σ'), en. iRight.
      iExists op, x, k; eauto. }
    iIntros (fs' α0 en0) "Hst Hlc". rewrite internal_step_vis.
    iAssert (gState_recomp rest σ' ≡ fs' ∧ Tick β ≡ Tick α0 ∧ en ≡ en0)%I
      with "[Hreify Hst]" as "[Hst [Hb Hen]]".
    { iRewrite "Hreify" in "Hst".
      do 2 rewrite prod_equivI; simpl.
      iDestruct "Hst" as "(Hst & G)".
      iFrame "G".
      done.
    }
    iEval (rewrite Hfs) in "Hgst".
    iMod (state_interp_has_state_idx_update i σ' with "Hgst Hlst") as "[Hgst Hlst]".
    iModIntro. iNext. iModIntro.
    iMod "Hcl2" as "_".
    iMod ("H" with "Hlc Hlst") as "[H1 H2]".
    iModIntro. iRewrite -"Hst".
    iRewrite -"Hb".
    iFrame "Hgst H1".
    iApply (internal_eq_rewrite with "Hen");
      last iExact "H2".
    intros m t1 t2 H.
    apply big_opL_ne_2; first done.
    solve_proper.
  Qed.

  Lemma wp_reify  E1 s Φ i (lop : opid (sReifier_ops (rs !!! i)))
    x k σ σ' β en :
    let op : opid F := (existT i lop) in
    (∀ rest, reify (Vis op x k)  (gState_recomp rest σ) ≡ (gState_recomp rest σ', Tick β, en)) →
    has_state_idx i σ
    -∗ ▷ (£ 1 -∗ has_state_idx i σ'
          -∗ WP β @ s;E1 {{ Φ }}
                      ∗ [∗ list] i ↦ ef ∈ en, WP ef @ s; ⊤ {{ _, True }})
    -∗ WP (Vis op x k) @ s;E1 {{ Φ }}.
  Proof.
    intros op Hr.
    iIntros "Hlst H".
    iApply wp_reify_idx.
    iModIntro. iExists σ, σ', β, en.
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
    iIntros (σ' β en) "Hst". iExFalso.
    iApply internal_step_err. done.
  Qed.

  Lemma wp_stuckness_mono α E1 (s1 s2 : error → Prop) Φ :
    (∀ e, s1 e → s2 e) →
    WP α @ s1;E1 {{ Φ }} ⊢ WP α @ s2;E1 {{ Φ }}.
  Proof.
    intros hse. iIntros "H1".
    iLöb as "IH" forall (α E1 Φ).
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
      iIntros (σ' β en) "Hst Hlc".
      iMod ("H" with "Hst Hlc") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iMod "H" as "[$ [G1 G2]]".
      iModIntro.
      iSplitL "IH G1".
      + by iApply ("IH" with "G1").
      + iInduction en as [| en] "IH'"; first done.
        rewrite !big_opL_cons.
        iDestruct "G2" as "[G2 G3]".
        iSplitL "G2".
        * by iApply ("IH" with "G2").
        * by iApply ("IH'" with "[$H1] [$Hs]").
  Qed.

  (** "adequacy" statements *)
  Lemma wp_internal_step α σ β σ' en s Ψ :
    ⊢ internal_step α σ β σ' en -∗ state_interp σ -∗ WP α @ s {{ Ψ }}
      -∗ £ 2 ={⊤}=∗ state_interp σ'
                  ∗ WP β @ s {{ Ψ }}
                  ∗ [∗ list] ef ∈ en, WP ef @ s {{ λne _ : ITVO, True }}.
  Proof.
    iIntros "Hstep Hs H [Hlc Hlc']".
    rewrite (wp_unfold α). iDestruct "H" as "[H|[Ha H]]".
    - iExFalso. iDestruct "H" as (αv) "[H _]".
      iApply (internal_step_ITV with "H Hstep").
    - iSpecialize ("H" with "Hs"). iDestruct "H" as "[_ H]".
      iMod "H" as "H".
      iMod ("H" with "Hstep Hlc'") as "H".
      iApply (fupd_trans ∅ ∅).
      iApply (lc_fupd_elim_later with "Hlc").
      iNext.
      iMod "H" as "H".
      iMod "H" as "[H1 [H2 H3]]".
      iModIntro.
      iFrame.
  Qed.

  Lemma wp_internal_steps α σ β σ' en m s Ψ :
    ⊢ internal_steps α σ β σ' en m -∗ state_interp σ -∗ WP α @ s {{ Ψ }}
      -∗ £ (3 * m) ={⊤}=∗ state_interp σ'
                        ∗ WP β @ s {{ Ψ }}
                        ∗ [∗ list] ef ∈ en, WP ef @ s {{ λne _ : ITVO, True }}.
  Proof.
    iIntros "Hstep Hs H [Hlc Hlc']".
    iInduction m as [| m] "IH" forall (α σ en).
    - rewrite internal_steps_0.
      iDestruct "Hstep" as "(H1 & H2 & H3)".
      iRewrite "H1" in "H".
      iRewrite "H2" in "Hs".
      iModIntro.
      iFrame "Hs H".
      iApply (internal_eq_rewrite _ _ with "[H3]");
        [| iApply internal_eq_sym; iExact "H3" |].
      + intros m x1 x2 Hx. apply big_opL_ne_2; first done.
        solve_proper.
      + by rewrite big_opL_nil.
    - rewrite internal_steps_S.
      rewrite lc_succ.
      iDestruct "Hlc" as "(Hlcone & Hlcrest)".
      rewrite !Nat.add_0_r.
      iEval (rewrite lc_split lc_succ) in "Hlc'".
      iDestruct "Hlc'" as "((Hlcone'' & Hlcrest'') & Hlcone' & Hlcrest')".
      iDestruct "Hstep" as "(%γ & %σ'' & %l' & %l'' & H1 & H2 & H3)".
      iCombine "Hlcone' Hlcone''" as "Hlctwo".
      iMod (wp_internal_step with "H2 Hs H Hlctwo") as "(G1 & G2 & G3)".
      iDestruct (lc_fupd_elim_later ⊤ with "Hlcone H3") as "G4".
      iSpecialize ("IH" $! γ σ'' l'' with "G4 G1 G2 Hlcrest").
      rewrite lc_split.
      iSpecialize ("IH" with "[$Hlcrest' $Hlcrest'']").
      do 2 iMod "IH".
      iModIntro.
      iDestruct "IH" as "(IH1 & IH2 & IH3)".
      iFrame "IH1 IH2".
      iApply (internal_eq_rewrite _ _ with "[H1]");
        [| iApply internal_eq_sym; iExact "H1" |].
      + intros k x1 x2 Hx. apply big_opL_ne_2; first done.
        solve_proper.
      + rewrite big_opL_app.
        by iFrame "G3 IH3".
  Qed.

  Lemma wp_tp_internal_step αs σ βs σ' s Ψs :
    ⊢ tp_internal_step αs σ βs σ' -∗ state_interp σ
      -∗ ([∗ list] x;Ψ ∈ αs;Ψs, WP x @ s {{ Ψ }})
      -∗ ∀ βs' βs'',
    βs ≡ βs' ++ βs''
    -∗ length βs' ≡ length αs
    -∗ £ 2 ={⊤}=∗ state_interp σ'
                ∗ ([∗ list] x;Ψ ∈ βs';Ψs, WP x @ s {{ Ψ }})
                ∗ ([∗ list] x ∈ βs'', WP x @ s {{ constO True }}).
  Proof.
    iIntros "Hstep Hs H %βs' %βs'' #Heq %Hlen Hlc".
    iDestruct "Hstep" as "(%α0 & %α1 & %γ & %γ' & %en & #H1 & #H2 & Hstep)".
    iAssert ([∗ list] x;Ψ ∈ (α0 ++ γ :: α1);Ψs, WP x @ s {{ Ψ }})%I with "[H]" as "H".
    {
      iApply (internal_eq_rewrite _ _ (λ y, [∗ list] x;Ψ ∈ y;Ψs, WP x @ s {{ Ψ }})%I
               with "H1");
        last iExact "H".
      intros k x1 x2 Hx.
      apply big_sepL2_ne_2; first done.
      - reflexivity.
      - solve_proper.
    }
    iDestruct (big_sepL2_app_inv_l with "H") as "(%l2 & %l2' & %Ψl & G1 & G2)".
    iDestruct (big_sepL2_cons_inv_l with "G2") as "(%x2 & %l2'' & %HEQ & G2 & G3)".
    iDestruct (wp_internal_step with "Hstep Hs G2 Hlc") as "G4".
    iMod "G4" as "(G4 & G5 & G6)".
    iModIntro.
    iFrame "G4".
    iAssert (βs'' ≡ en)%I as "HEQ''".
    {
      iRewrite "Heq" in "H2".
      iPoseProof (f_equivI (drop (length βs')) with "H2") as "H3".
      rewrite drop_app_length Hlen.
      iAssert (length αs ≡ length (α0 ++ γ' :: α1))%I as "H4".
      {
        iRewrite "H1".
        rewrite !app_length /=.
        iApply (f_equivI (plus (length α0))).
        done.
      }
      iRewrite "H4" in "H3".
      rewrite {2} app_comm_cons.
      rewrite app_assoc drop_app drop_all app_nil_l.
      rewrite Nat.sub_diag drop_0.
      iDestruct (f_equivI (drop (length (α0 ++ γ' :: α1))) with "H2") as "H5".
      iDestruct (internal_eq_sym with "H5") as "H6"; iClear "H5".
      rewrite drop_app.
      rewrite Nat.sub_diag drop_0.
      rewrite drop_all app_nil_l.
      iRewrite - "H4" in "H6".
      rewrite -Hlen.
      rewrite drop_app drop_all app_nil_l Nat.sub_diag drop_0.
      done.
    }
    iSplitL "G1 G5 G3".
    {
      iAssert (βs' ≡ α0 ++ γ' :: α1)%I as "HEQ'".
      {
        iRewrite "Heq" in "H2".
        iDestruct (f_equivI (take (length βs')) with "H2") as "H3".
        rewrite take_app Nat.sub_diag take_0 app_nil_r firstn_all.
        rewrite Hlen.
        iRewrite "H1" in "H3".
        rewrite {2} app_comm_cons app_assoc.
        rewrite take_app.
        iAssert (length (α0 ++ γ :: α1) ≡ length (α0 ++ γ' :: α1))%I as "H4".
        {
          iPureIntro.
          by rewrite !app_length /=.
        }
        iRewrite "H4" in "H3".
        rewrite firstn_all Nat.sub_diag take_0 app_nil_r.
        done.
      }
      iApply (internal_eq_rewrite _ _ (λ y, [∗ list] x;Ψ ∈ y;Ψs, WP x @ s {{ Ψ }})%I
               with "[HEQ']");
        [| iApply internal_eq_sym; iExact "HEQ'" |].
      {
        intros k y1 y2 Hy.
        by apply big_sepL2_ne_2; [| done | solve_proper].
      }
      rewrite Ψl.
      iApply (big_sepL2_app with "G1").
      rewrite HEQ.
      iApply (big_sepL2_cons with "[-]").
      iFrame "G5 G3".
    }
    {
      iApply (internal_eq_rewrite _ _ (λ y, [∗ list] x ∈ y, WP x @ s {{ constO True }})%I
               with "[HEQ'']");
        [| iApply internal_eq_sym; iExact "HEQ''" |].
      {
        intros k y1 y2 Hy.
        apply big_opL_ne_2; first solve_proper.
        repeat intros; solve_proper.
      }
      iFrame "G6".
    }
  Qed.

  Lemma tp_internal_steps_decomp αs βs σ σ' k :
    ⊢ £ k -∗ tp_internal_steps αs σ βs σ' k
      ={⊤}=∗ ∃ β1 β2 : listO IT, βs ≡ β1 ++ β2 ∗ length αs ≡ length β1.
  Proof.
    iInduction k as [| k] "IH" forall (αs σ); iIntros "Hlc H".
    - rewrite tp_internal_steps_0.
      iDestruct "H" as "(H1 & _)".
      iExists βs, [].
      rewrite app_nil_r.
      iRewrite "H1".
      done.
    - rewrite tp_internal_steps_S.
      iDestruct "H" as "(%t1 & %t2 & G1 & G2)".
      iDestruct "Hlc" as "(J1 & J2)".
      iMod (lc_fupd_elim_later ⊤ (tp_internal_steps t1 t2 βs σ' k) with "J1 G2") as "J".
      iDestruct (tp_internal_step_decomp with "G1") as "(%u1 & %u2 & #G1' & #G2)".
      iRewrite "G1'" in "J".
      iMod ("IH" $! (u1 ++ u2) t2 with "J2 J") as "(%p1 & %p2 & K1 & %K2)".
      iRewrite "K1".
      iRewrite "G2".
      iModIntro.
      iExists (take (length u1) p1), ((drop (length u1) p1) ++ p2).
      iSplit.
      + rewrite app_assoc.
        iApply (f_equivI (flip app p2) with "[]").
        by rewrite take_drop.
      + rewrite firstn_length_le; first done.
        rewrite -K2.
        rewrite app_length.
        lia.
  Qed.

  (* k too many credits, but i ain't greedy *)
  Lemma wp_tp_internal_steps αs σ βs σ' s Ψs k :
    ⊢ tp_internal_steps αs σ βs σ' k -∗ state_interp σ
      -∗ ([∗ list] x;Ψ ∈ αs;Ψs, WP x @ s {{ Ψ }})
      -∗ ∀ βs' βs'',
    βs ≡ βs' ++ βs''
    -∗ length βs' ≡ length αs
    -∗ £ (k * k + 2 * k) ={⊤}=∗ state_interp σ' ∗
                        ([∗ list] x;Ψ ∈ βs';Ψs, WP x @ s {{ Ψ }})
                      ∗ ([∗ list] x ∈ βs'', WP x @ s {{ constO True }}).
  Proof.
    iInduction k as [| k] "IH" forall (αs βs σ Ψs); iIntros "Hstep Hs H %βs' %βs'' #HEQ %Hlen Hlc".
    - rewrite tp_internal_steps_0.
      iModIntro.
      iDestruct "Hstep" as "(#H1 & H2)".
      iRewrite - "H2".
      iFrame "Hs".
      iAssert (βs'' ≡ [])%I as "HEQ'".
      {
        iDestruct (f_equivI (drop (length βs')) with "HEQ") as "H2".
        rewrite Hlen.
        rewrite -{2} Hlen.
        iRewrite "H1" in "H2".
        rewrite drop_app Nat.sub_diag drop_0 drop_all.
        rewrite drop_all app_nil_l.
        iApply internal_eq_sym.
        done.
      }
      iSplitL "H".
      {
        iDestruct (internal_eq_rewrite _ _
                     (λ y,
                       ([∗ list] x;Ψ ∈ y;Ψs, WP x @ s {{ Ψ }}))%I
                    with "[H1 HEQ HEQ'] H") as "H2".
        {
          intros m y1 y2 Hy.
          apply big_sepL2_ne_2; [| reflexivity | solve_proper].
          by rewrite Hy.
        }
        {
          iRewrite "H1".
          iRewrite "HEQ".
          iRewrite "HEQ'".
          rewrite app_nil_r.
          iPureIntro.
          reflexivity.
        }
        iExact "H2".
      }
      {
        iApply (internal_eq_rewrite _ _
                     (λ y,
                       ([∗ list] x ∈ y, WP x @ s {{ constO True }}))%I
                    with "[HEQ']").
        {
          intros m y1 y2 Hy.
          apply big_opL_ne_2; first done.
          solve_proper.
        }
        {
          iApply internal_eq_sym; iExact "HEQ'".
        }
        done.
      }
    - rewrite tp_internal_steps_S.
      iPoseProof (big_sepL2_alt with "H") as "HT".
      iDestruct "HT" as "[%HT1 HT2]".
      iPoseProof (big_sepL2_alt (λ _ x y, WP x @ s {{ y }}%I) with "[HT2]") as "H".
      {
        iSplit; first (iPureIntro; apply HT1).
        iApply "HT2".
      }
      iDestruct "Hstep" as "(%γ & %σ'' & #H1 & H2)".
      iDestruct (tp_internal_step_decomp with "H1") as "(%γs' & %γs'' & F1 & %F2)".
      iDestruct (wp_tp_internal_step with "H1 Hs H") as "H3".
      iClear "H1".
      iSpecialize ("H3" $! γs' γs'' with "F1 []").
      { by rewrite F2. }
      rewrite /= lc_succ plus_n_Sm Nat.add_0_r Nat.mul_succ_r.
      iDestruct "Hlc" as "[Hlc1 [[Hlc2 [Hlc4 Hlc5]] [Hlc6 [Hlc7 [Hlc8 Hlc9]]]]]".
      iMod (lc_fupd_elim_later ⊤ with "Hlc1 H2") as "#H2".
      iMod ("H3" with "[Hlc7 Hlc8]") as "(H3 & H4)"; first by iSplitL "Hlc7".
      set (F := (λ _, True%I) : ITV -d> iProp).
      iAssert ([∗ list] x;Ψ ∈ (γs' ++ γs'');(Ψs ++ replicate (length γs'') F), WP x @ s {{ Ψ }})%I with "[H4]" as "H5".
      {
        iDestruct "H4" as "(H4 & H5)".
        iApply (big_sepL2_app with "H4").
        iApply big_sepL2_alt.
        iSplit.
        - iPureIntro.
          by rewrite replicate_length.
        - iClear "IH HEQ H2 F1".
          iInduction γs'' as [| x ens] "IH"; first done.
          iDestruct "H5" as "(H5 & H6)".
          simpl.
          iFrame "H5".
          iApply "IH".
          iFrame "H6".
      }
      iSpecialize ("IH" $! (γs' ++ γs'')
                     βs σ'' (Ψs ++ replicate (length γs'') F) with "[H2] H3 H5").
      {
        iRewrite "F1" in "H2".
        iFrame "H2".
      }
      iMod (tp_internal_steps_decomp with "Hlc2 H2") as "(%a1 & %a2 & #A1 & %A2)".
      iSpecialize ("IH" $! a1 a2 with "A1 [] [Hlc4 Hlc5 Hlc6]").
      {
        rewrite -A2.
        by iRewrite "F1".
      }
      {
        iSplitL "Hlc4"; first done.
        iSplitL "Hlc5"; done.
      }
      iMod "IH".
      iModIntro.
      iDestruct "IH" as "(IH1 & IH2 & IH3)".
      iFrame "IH1".
      iPoseProof (big_sepL2_alt with "IH2") as "HP".
      iDestruct "HP" as "[%HP1 HP2]".
      iPoseProof (big_sepL2_alt (λ _ x y, WP x @ s {{ y }}%I) with "[HP2]") as "IH2".
      {
        iSplit; first (iPureIntro; apply HP1).
        iApply "HP2".
      }
      iAssert ([∗ list] x;Ψ ∈ a2;(replicate (length a2) F), WP x @ s {{ Ψ }})%I with "[IH3]" as "H5".
      {
        iApply big_sepL2_alt.
        iSplit.
        - iPureIntro.
          by rewrite replicate_length.
        - iClear "A1".
          iInduction a2 as [| x ens] "IH"; first done.
          iDestruct "IH3" as "(H5 & H6)".
          simpl.
          iFrame "H5".
          iApply "IH".
          iFrame "H6".
      }
      iPoseProof (big_sepL2_app with "IH2 H5") as "IH".
      rewrite -app_assoc.
      iDestruct (internal_eq_rewrite _ _
                (λ y,
                  ([∗ list] x;x' ∈ y;_, WP x @ s {{ x' }}))%I
               with "[A1] IH") as "IH".
      {
        intros m y1 y2 Hy.
        apply big_sepL2_ne_2; first done.
        - solve_proper.
        - solve_proper.
      }
      {
        iRewrite - "A1".
        iApply "HEQ".
      }
      rewrite HT1 in Hlen.
      iDestruct (big_sepL2_app_inv with "IH") as "[IH1 IH2]".
      { by left. }
      iFrame "IH1".
      rewrite -replicate_add.
      iPoseProof (big_sepL2_alt with "IH2") as "HP".
      iDestruct "HP" as "[%HW1 HW2]".
      iPoseProof (big_sepL2_alt (λ _ x y, WP x @ s {{ y }}%I) with "[HW2]") as "IH2".
      {
        iSplit; first (iPureIntro; apply HW1).
        iApply "HW2".
      }
      iPoseProof (big_sepL2_replicate_r with "IH2") as "HP".
      {
        rewrite replicate_length in HW1.
        done.
      }
      iApply "HP".
  Qed.

  Lemma wp_external_step α σ β σ' en s Ψ :
    external_step α σ β σ' en →
    state_interp σ ∗ WP α @ s {{ Ψ }}
    ⊢  £ 2
       ={⊤}=∗ (state_interp σ'
               ∗ WP β @ s {{ Ψ }}
               ∗ ([∗ list] ef ∈ en, WP ef @ s {{ λne _ : ITVO, True }})).
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (internal_step α σ β σ' en) as "Hst".
    { by iApply external_step_internal_step. }
    iApply (wp_internal_step with "Hst Hs HIC").
  Qed.

  Lemma wp_external_steps α σ β σ' en k s Ψ :
    external_steps α σ β σ' en k →
    state_interp σ ∗ WP α @ s {{ Ψ }}
    ⊢  £ (3 * k)
       ={⊤}=∗ (state_interp σ'
               ∗ WP β @ s {{ Ψ }}
               ∗ ([∗ list] ef ∈ en, WP ef @ s {{ λne _ : ITVO, True }})).
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (internal_steps α σ β σ' en k) as "Hst".
    { by iApply external_steps_internal_steps. }
    iApply (wp_internal_steps with "Hst Hs HIC").
  Qed.

  Lemma wp_tp_external_step αs σ βs σ' s Ψs :
    tp_external_step αs σ βs σ' →
    state_interp σ ∗ ([∗ list] x;Ψ ∈ αs;Ψs, WP x @ s {{ Ψ }})
      ⊢  ∀ βs' βs'',
    βs ≡ βs' ++ βs''
    -∗ length βs' ≡ length αs
      -∗ £ 2 ={⊤}=∗ (state_interp σ'
                     ∗ ([∗ list] x;Ψ ∈ βs';Ψs, WP x @ s {{ Ψ }})
                     ∗ ([∗ list] x ∈ βs'', WP x @ s {{ constO True }})).
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (tp_internal_step αs σ βs σ') as "Hst".
    { by iApply tp_external_step_tp_internal_step. }
    iApply (wp_tp_internal_step with "Hst Hs HIC").
  Qed.

  Lemma wp_tp_external_steps αs σ βs σ' s Ψs k :
    tp_external_steps αs σ βs σ' k →
    state_interp σ ∗ ([∗ list] x;Ψ ∈ αs;Ψs, WP x @ s {{ Ψ }})
      ⊢  £ (k * k + 2 * k) ={⊤}=∗ (state_interp σ' ∗ ([∗ list] x;Ψ ∈ (take (length αs) βs);Ψs, WP x @ s {{ Ψ }}) ∗ ([∗ list] x ∈ drop (length αs) βs, WP x @ s {{ constO True }})).
  Proof.
    iIntros (Hst) "[Hs HIC]".
    iAssert (tp_internal_steps αs σ βs σ' k) as "Hst".
    { by iApply tp_external_steps_tp_internal_steps. }
    iPoseProof (wp_tp_internal_steps with "Hst Hs HIC") as "HTTT".
    iSpecialize ("HTTT" $! (take (length αs) βs) (drop (length αs) βs)).
    iSpecialize ("HTTT" with "[] []").
    { iPureIntro. by rewrite take_drop. }
    { rewrite take_length_le; first done. by eapply tp_external_steps_mono. }
    iApply "HTTT".
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

  Lemma wp_external_steps_internal_safe α σ β σ' l k s Ψ :
    external_steps α σ β σ' l k →
    state_interp σ ∗ WP α @ s {{ Ψ }}
      ⊢  £ (3 * k + 2) ={⊤,∅}=∗
        (⌜is_Some (IT_to_V β)⌝
           ∨ (∃ β2 σ2 l2, internal_step β σ' β2 σ2 l2)
           ∨ (∃ e, β ≡ Err e ∧ ⌜s e⌝)).
  Proof.
    intros Hst. rewrite wp_external_steps//.
    iIntros "H [Hlc [Hone Htwo]]". iSpecialize ("H" with "Hlc").
    iMod "H" as "[Hs H]".
    rewrite wp_unfold. iDestruct "H" as "[[H | [Hb H]] G]".
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
        {
          iExFalso. iDestruct "Hst" as (α' σ'0 en') "Hst".
          iRewrite "Heq" in "Hst".
          iApply (internal_step_err with "Hst").
        }
        iModIntro. done.
      + iRight. iLeft.
        iMod ("H" with "Hs") as "[#Hst H]".
        iDestruct "Hst" as "[(%t1 & %t2 & %t3 & Hst)|Hst]"; last first.
        {
          iExFalso. iDestruct "Hst" as (e') "[Hst ?]".
          iApply "Heq". eauto with iFrame.
        }
        iExists t1, t2, t3.
        iFrame "Hst".
        iModIntro.
        done.
  Qed.

  Lemma wp_external_steps_val α σ βv σ' l k s Ψ `{!NonExpansive Ψ} :
    external_steps α σ (IT_of_V βv) σ' l k →
    state_interp σ ∗ WP α @ s {{ Ψ }}
                 ⊢ £ (3*k) ={⊤}=∗ Ψ βv.
  Proof.
    intros Hst. rewrite wp_external_steps //.
    iIntros "H Hk". iSpecialize ("H" with "Hk").
    iMod "H" as "[Hs H]".
    rewrite wp_unfold. iDestruct "H" as "[[H | [Hb H]] G]".
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
  Notation internal_step rs := (internal_step (rG rs)).
  Notation internal_steps rs := (internal_steps (rG rs)).
  Notation tp_internal_step rs := (tp_internal_step (rG rs)).
  Notation tp_internal_steps rs := (tp_internal_steps (rG rs)).
  Notation external_step rs := (external_step (rG rs)).
  Notation external_steps rs := (external_steps (rG rs)).
  Notation tp_external_step rs := (tp_external_step (rG rs)).
  Notation tp_external_steps rs := (tp_external_steps (rG rs)).

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
       ∃ σ y σ' β l,
       has_state_idx rs i σ
       ∗ sReifier_re (rs !!! i) lop (x, σ, k) ≡ Some (y, σ', l)
       ∗ y ≡ Next β
       ∗ ▷ (£ 1 -∗ has_state_idx rs i σ'
            ={E2,E1}=∗ wp rs β s E1 Φ
                     ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True))))
    -∗ wp rs (Vis op x k) s E1 Φ.
  Proof.
    intros op x k.
    iIntros "H".
    iApply wp_reify_idx.
    iMod "H" as (σ y σ' β l) "[Hlst [Hreify [Hk H]]]".
    iModIntro. iExists σ, σ', β, (listO_map Tau l).
    iFrame "Hlst".
    iIntros (rest).
    iFrame "H".
    iAssert (gReifiers_re rs _ _ op (x, gState_recomp rest σ, _)
               ≡ Some (y, gState_recomp rest σ', l))%I
      with "[Hreify]"  as "Hgreify".
    { rewrite (@gReifiers_re_idx _ CtxDep).
      iAssert ((optionO_map (prodO_map (prodO_map idfun (gState_recomp rest)) idfun) (sReifier_re (rs !!! i) lop (x, σ, k)))
                 ≡ optionO_map (prodO_map (prodO_map idfun (gState_recomp rest)) idfun)
                 (Some (y, σ', l)))%I with "[Hreify]" as "H".
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
    (|={E1,E2}=>  ∃ σ y σ' β l,
       has_state_idx rs i σ
       ∗ sReifier_re (rs !!! i) lop (x, σ) ≡ Some (y, σ', l)
       ∗ k y ≡ Next β
       ∗ ▷ (£ 1 -∗ has_state_idx rs i σ'
            ={E2,E1}=∗ wp rs β s E1 Φ
                     ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True))))
    -∗ wp rs (Vis op x k) s E1 Φ.
  Proof.
    intros op x k.
    iIntros "H".
    iApply wp_reify_idx.
    iMod "H" as (σ y σ' β l) "[Hlst [Hreify [Hk H]]]".
    iModIntro. iExists σ, σ', β, (listO_map Tau l).
    iFrame "Hlst".
    iIntros (rest).
    iFrame "H".
    iAssert (@gReifiers_re _ NotCtxDep rs _ _ op (x, gState_recomp rest σ)
               ≡ Some (y, gState_recomp rest σ', l))%I
      with "[Hreify]"  as "Hgreify".
    { pose proof (@gReifiers_re_idx n NotCtxDep i rs (IT rs)) as J.
      simpl in J.
      simpl.
      rewrite J; clear J.
      iAssert (optionO_map (prodO_map (prodO_map idfun (gState_recomp rest)) idfun)
                 (sReifier_re (rs !!! i) lop (x, σ))
                 ≡ optionO_map (prodO_map (prodO_map idfun (gState_recomp rest)) idfun)
                 (Some (y, σ', l)))%I with "[Hreify]" as "H".
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
    (|={E1,E2}=> ∃ σ y σ' β l,
       has_substate rs σ
       ∗ sReifier_re sR op (x, σ, (k ◎ subEff_outs)) ≡ Some (y, σ', l)
       ∗ y ≡ Next β
       ∗ ▷ (£ 1 -∗ has_substate rs σ'
            ={E2,E1}=∗ wp rs β s E1 Φ
                     ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True))))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    iIntros "H".
    iApply wp_reify_idx_ctx_dep.
    iMod "H" as (σ y σ' β l) "[Hlst [Hreify [Hk H]]]".
    iModIntro.
    iExists (sR_state σ), y, (sR_state σ'), β, l.
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
    (|={E1,E2}=> ∃ σ y σ' β l,
       has_substate rs σ
       ∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
       ∗ k (subEff_outs y) ≡ Next β
       ∗ ▷ (£ 1 -∗ has_substate rs σ'
            ={E2,E1}=∗ wp rs β s E1 Φ
                     ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True))))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    iIntros "H".
    iApply wp_reify_idx_ctx_indep.
    iMod "H" as (σ y σ' β l) "[Hlst [Hreify [Hk H]]]".
    iModIntro.
    iExists (sR_state σ),(subEff_outs y), (sR_state σ'), β.
    iExists l.
    iFrame "Hlst H Hk".
    by iApply subReifier_reify_idxI_ctx_indep.
  Qed.

  Lemma wp_subreify_ctx_dep (rs : gReifiers CtxDep n)
    `{!@stateG _ CtxDep rs A _ Σ} E1 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs) (y : laterO (IT rs))
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β l :
    sReifier_re sR op (x, σ, (k ◎ subEff_outs)) ≡ Some (y, σ', l) →
    y ≡ Next β →
    has_substate rs σ
    -∗ ▷ (£ 1 -∗ has_substate rs σ' -∗ wp rs β s E1 Φ ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True)))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
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
    (σ σ' : sReifier_state sR ♯ IT rs) β l :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate rs σ
    -∗ ▷ (£ 1 -∗ has_substate rs σ' -∗ wp rs β s E1 Φ
                                     ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True)))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    intros HSR Hk.
    iIntros "Hlst H".
    iApply (wp_reify with "Hlst H").
    intros rest.
    rewrite Tick_eq. rewrite -Hk.
    rewrite reify_vis_eq_ctx_indep //.
    by apply (subReifier_reify (a := NotCtxDep)).
  Qed.

  Global Instance subEffCtxIndep a (rs : gReifiers a n)
    sR
    `{!subReifier (sReifier_NotCtxDep_min sR a) rs}
    : subEff (sReifier_ops sR) (F rs).
  Proof.
    refine subReifier_subEff.
  Defined.

  Lemma wp_subreify_ctx_indep_lift (rs : gReifiers CtxDep n)
    `{!@stateG _ CtxDep rs A _ Σ} E1 s Φ sR
    `{!subReifier (sReifier_NotCtxDep_CtxDep sR) rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs)
    (y : Outs (sReifier_ops sR op) ♯ IT rs)
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β l :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate rs σ
    -∗ ▷ (£ 1 -∗ has_substate rs σ'
          -∗ wp rs β s E1 Φ
           ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True)))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    intros HSR Hk.
    iIntros "Hlst H".
    iApply (wp_reify with "Hlst H").
    intros rest.
    rewrite Tick_eq. rewrite -Hk.
    rewrite reify_vis_eq_ctx_dep //.
    rewrite Hk.
    Opaque prodO_map.
    rewrite <-(@subReifier_reify n CtxDep (sReifier_NotCtxDep_CtxDep sR) rs _
                (IT rs) _ op x (Next β) (k ◎ subEff_outs) σ σ').
    {
      simpl.
      do 3 f_equiv.
      intro; simpl.
      by rewrite ofe_iso_12.
    }
    simpl.
    match goal with
    | |- context G [?a <$> ?b] =>
        assert (a <$> b ≡ a <$> (Some (y, σ', l))) as ->
    end.
    {
      f_equiv.
      apply HSR.
    }
    simpl.
    Transparent prodO_map.
    simpl.
    rewrite Hk.
    reflexivity.
  Qed.

  Lemma wp_subreify_ctx_indep_lift' a (rs : gReifiers a n)
    `{!@stateG _ a rs A _ Σ} E1 s Φ sR
    `{!subReifier (sReifier_NotCtxDep_min sR a) rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs)
    (y : Outs (sReifier_ops sR op) ♯ IT rs)
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β l :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate rs σ
    -∗ ▷ (£ 1 -∗ has_substate rs σ'
          -∗ wp rs β s E1 Φ
           ∗ ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True)))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    destruct a.
    - simpl in *|-.
      intros HSR Hk.
      iIntros "Hlst H".
      iApply wp_subreify_ctx_dep'.
      iModIntro.
      iExists σ.
      simpl in *|-.
      iExists (k (subEff_outs y)).
      iExists σ'.
      iExists β.
      iExists l.
      iFrame "Hlst".
      iSplit.
      + Opaque prodO_map.
        simpl.
        rewrite Hk.
        rewrite HSR.
        Transparent prodO_map.
        simpl.
        rewrite Hk.
        done.
      + iSplit; first done.
        iNext.
        iIntros "H1 H2".
        iModIntro.
        iApply ("H" with "[$]").
        iFrame "H2".
    - simpl in *|-.
      intros HSR Hk.
      iIntros "Hlst H".
      assert ((sReifier_NotCtxDep_min sR NotCtxDep)
              = sR) as HEQ.
      {
        unfold sReifier_NotCtxDep_min.
        destruct sR.
        reflexivity.
      }
      iApply (wp_reify with "Hlst H").
      intros rest.
      rewrite Tick_eq. rewrite -Hk.
      rewrite reify_vis_eq_ctx_indep //.
      rewrite <-(@subReifier_reify n NotCtxDep (sReifier_NotCtxDep_min sR _) rs _
                  (IT rs) _ op x y σ σ' rest); first by f_equiv.
      simpl.
      apply HSR.
  Qed.

  Lemma wp_subreify_ctx_indep_lift'' a (rs : gReifiers a n)
    `{!@stateG _ a rs A _ Σ} E1 E2 s Φ sR
    `{!subReifier (sReifier_NotCtxDep_min sR a) rs}
    (op : opid (sReifier_ops sR)) (x : Ins (sReifier_ops sR op) ♯ (IT rs))
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs)) :
    (|={E1,E2}=> ∃ σ y σ' β l,
       has_substate rs σ ∗
         sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
       ∗ k (subEff_outs y) ≡ Next β
       ∗ ▷ (£ 1 -∗ has_substate rs σ'
            ={E2,E1}=∗ wp rs β s E1 Φ ∗
                       ([∗ list] ef ∈ listO_map Tau l, wp rs ef s ⊤ (λ _ : ITV rs, True))))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    destruct a.
    - iIntros "H".
      iApply wp_reify_idx_ctx_dep.
      iMod "H" as (σ y σ' β l) "[Hlst [#Hreify [#Hk H]]]".
      iModIntro.
      iExists (sR_state σ), (k (subEff_outs y)).
      iExists _, β, l.
      iSplitL "Hlst".
      { iFrame "Hlst". }
      iSplitR "Hk H"; first last.
      {
        iFrame "Hk".
        iApply "H".
      }
      epose proof (subReifier_reify_idxI_ctx_dep (Σ := Σ)
                     (sReifier_NotCtxDep_min sR CtxDep) op x (k (subEff_outs y))
                     (k ◎ subEff_outs) σ σ') as G.
      assert (k ≡ k ◎ ofe_iso_1 subEff_outs ◎ subEff_outs ^-1) as ->.
      { intro; simpl; by rewrite ofe_iso_12. }
      iApply G.
      Opaque prodO_map.
      simpl.
      iRewrite "Hreify".
      Transparent prodO_map.
      simpl.
      iPureIntro.
      do 3 f_equiv.
    - iApply wp_subreify_ctx_indep'.
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
  Notation internal_step := (internal_step rG).
  Notation internal_steps := (internal_steps rG).
  Notation tp_internal_step := (tp_internal_step rG).
  Notation tp_internal_steps := (tp_internal_steps rG).
  Notation external_step := (external_step rG).
  Notation external_steps := (external_steps rG).
  Notation tp_external_step := (tp_external_step rG).
  Notation tp_external_steps := (tp_external_steps rG).
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
          - iDestruct "Hsafe" as (α' σ' l') "Hsafe". iLeft.
            iExists (f α'), σ', l'. iApply (internal_step_hom with "Hsafe").
          - iDestruct "Herr" as (e) "[Herr %]".
            iRight. iExists e. iSplit; last done.
            iRewrite "Herr". rewrite hom_err//. }
        iIntros (σ' β l) "Hst".
        rewrite {1}internal_step_hom_inv. iDestruct "Hst" as "[%Ha | [_ Hst]]".
        { destruct Ha as [αv Ha]. rewrite Ha.
          iExFalso.
          iApply (option_equivI with "Hav"). }
        iDestruct "Hst" as (α') "[Hst Hb]".
        iIntros "Hlc".
        iMod ("H" with "Hst Hlc") as "H". iModIntro.
        iNext. iMod "H" as "H". iModIntro.
        iMod "H" as "[$ [H1 H2]]".
        iModIntro. iRewrite "Hb".
        iSplitR "H2"; last done.
        by iApply "IH".
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
  (α : IT _ A) σ βv σ' s l k (ψ : (ITV (gReifiers_ops rs) A) → Prop) :
  external_steps (gReifiers_sReifier rs) α σ (IT_of_V βv) σ' l k →
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
  iPoseProof (wp_external_steps with "[$Hs $Hic]") as "Hphi".
  { eassumption. }
  iMod ("Hphi" with "Hlc") as "[Hst [H1 H2]]".
  rewrite wp_val_inv; eauto.
  iMod "H1" as "H1".
  rewrite HΦψ. iFrame "H1".
  by iApply fupd_mask_intro_discard.
Qed.

Lemma wp_adequacy_tp cr Σ `{!invGpreS Σ} n a (rs : gReifiers a n)
  {A} `{!Cofe A} `{!statePreG rs A Σ}
  (α : (IT _ A)) σ β βv σ' s k (ψ : (ITV (gReifiers_ops rs) A) → Prop) :
  tp_external_steps (gReifiers_sReifier rs) [α] σ ((IT_of_V βv) :: β) σ' k →
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs A Σ},
     ∃ (Φs : list (ITV (gReifiers_ops rs) A -> iPropI Σ)),
       (Forall (λ f, (∀ n, Proper (dist n ==> dist n) f)) Φs) ∧
       (∀ βv, (from_option id (λ _, True%I) (head Φs)) βv ⊢ ⌜ψ βv⌝) ∧
       (£ cr ∗ has_full_state σ ⊢ [∗ list] x;Φ ∈ [α];Φs, WP@{rs} x @ s {{ Φ }})%I)
  → ψ βv.
Proof.
  intros Hst Hprf.
  cut (⊢ ⌜ψ βv⌝ : iProp Σ)%I.
  { intros HH. eapply uPred.pure_soundness; eauto. }
  eapply (step_fupdN_soundness_lc _ 0 (cr + (k * k + 2 * k))).
  intros Hinv. iIntros "[Hcr Hlc]".
  iMod (new_state_interp rs σ) as (sg) "[Hs Hs2]".
  destruct (Hprf Hinv sg) as (Φs & Hne & Hprf' & Hprf'').
  iPoseProof (Hprf'' with "[$Hcr $Hs2]") as "Hic".
  iPoseProof (wp_tp_external_steps with "[$Hs $Hic]") as "Hphi".
  { eassumption. }
  iMod ("Hphi" with "Hlc") as "[Hst H]".
  simpl.
  iDestruct "H" as "[H1  H2]".
  rewrite take_0.
  specialize (Hprf' βv).
  iPoseProof (big_sepL2_alt with "H1") as "H1".
  iDestruct "H1" as "[%HW1 HW2]".
  simpl in HW1.
  assert (∃ Φ, Φs = [Φ]) as HHH.
  { destruct Φs as [| b ?].
    - inversion HW1.
    - simpl in HW1.
      inversion HW1 as [HW2].
      destruct Φs.
      + exists b; done.
      + inversion HW2.
  }
  destruct HHH as [Φ ->].
  simpl.
  iDestruct "HW2" as "[HW2 _]".
  erewrite wp_val_inv; eauto.
  - iMod "HW2" as "H".
    iApply Hprf'.
    simpl in *.
    by iApply fupd_mask_intro_discard.
  - by rewrite Forall_singleton in Hne.
  - apply _.
Qed.

Lemma wp_safety cr Σ `{!invGpreS Σ} n a (rs : gReifiers a n)
  {A} `{!Cofe A} `{!statePreG rs A Σ} s l k
  (α β : IT (gReifiers_ops rs) A) (σ σ' : gReifiers_state rs ♯ IT (gReifiers_ops rs) A) :
  (∀ Σ P Q, @disjunction_property Σ P Q) →
  external_steps (gReifiers_sReifier rs) α σ β σ' l k →
  IT_to_V β ≡ None →
  (∀ `{H1 : !invGS_gen HasLc Σ} `{H2: !stateG rs A Σ},
     ∃ Φ, NonExpansive Φ ∧ (£ cr ∗ has_full_state σ ⊢ WP@{rs} α @ s {{ Φ }})%I)  →
  ((∃ β1 σ1 l1, external_step (gReifiers_sReifier rs) β σ' β1 σ1 l1)
   ∨ (∃ e, β ≡ Err e ∧ s e)).
Proof.
  Opaque internal_step.
  intros Hdisj Hstep Hbv Hwp.
  cut (⊢@{iProp Σ} (∃ β1 σ1 l1, internal_step (gReifiers_sReifier rs) β σ' β1 σ1 l1)
        ∨ (∃ e, β ≡ Err e ∧ ⌜s e⌝))%I.
  { intros [Hprf | Hprf]%Hdisj.
    - left.
      apply (internal_step_safe_external_step _ (Σ:=Σ)).
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
  iPoseProof (wp_external_steps_internal_safe with "[$Hs $Hic]") as "H".
  { eassumption. }
  iMod ("H" with "Hlc") as "[H | H]".
  { iDestruct "H" as (βv) "%Hbeta".
    exfalso. rewrite Hbeta  in Hbv.
    inversion Hbv. }
  iFrame "H".
  by iApply fupd_mask_intro_discard.
Qed.
