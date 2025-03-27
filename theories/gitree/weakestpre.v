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

Section state.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n) A `{!Cofe A}.
  Notation rG := (gReifiers_sReifier rs).
  Notation F := (sReifier_ops rG).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Let of_idx := (of_idx rs IT).

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

End state.

Arguments state_interp {_ _ _ _ _ _ _}.
Arguments has_state_idx {_ _ _ _ _ _ _}.
Arguments has_substate {_ _ _ _ _ _ _ _ _}.
Arguments state_interp_has_state_idx_update {_ _ _ _ _}.
Arguments state_interp_has_state_idx_agree {_ _ _ _ _}.
Arguments new_state_interp {_ _ _ _ _}.

Section GS.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n) A `{!Cofe A}.
  Notation rG := (gReifiers_sReifier rs).
  Notation F := (sReifier_ops rG).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).

  Class gitreeGS_gen (Σ : gFunctors) :=
    GitreeG {
        #[global] gitreeInvGS :: invGS Σ;
        #[global] gitreeStateGS :: stateG rs A Σ;
        state_interp_fun : nat → stateO → iProp Σ;
        aux_interp_fun : nat → iProp Σ;
        fork_post : ITV -> iProp Σ;
        #[global] fork_post_ne :: NonExpansive fork_post;
        num_later_per_step : nat → nat;
        state_interp_fun_mono n σ :
        state_interp_fun n σ ⊢ |={∅}=> state_interp_fun (S n) σ;
        #[global] state_interp_fun_ne n :: NonExpansive (state_interp_fun n);
        state_interp_fun_decomp n σ :
        state_interp_fun n σ ⊣⊢ aux_interp_fun n ∗ state_interp σ;
      }.
End GS.

Arguments gitreeInvGS {_ _ _ _ _ _ _}.
Arguments gitreeStateGS {_ _ _ _ _ _ _}.
Arguments state_interp_fun {_ _ _ _ _ _ _}.
Arguments fork_post {_ _ _ _ _ _ _}.
Arguments num_later_per_step {_ _ _ _ _ _ _}.
Arguments aux_interp_fun {_ _ _ _ _ _ _}.

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

  Context `{!gitreeGS_gen rs A Σ}.

  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Definition stuckness := error → Prop.

  (** Weakest precondition *)
  Program Definition wp_pre (s : stuckness)
     (self : (ITV -d> iProp) -n> coPsetO -n> IT -n> iProp)
    : (ITV -d> iProp) -n> coPsetO -n> IT -n> iProp
    := λne Φ E α,
      ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E}=> Φ αv)
       ∨ (IT_to_V α ≡ None ∧ ∀ σ ns,
            state_interp_fun ns σ
            ={E,∅}=∗ ((∃ α' σ' en, internal_step α σ α' σ' en)
                      ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))
            ∧ (∀ σ' β en, internal_step α σ β σ' en
                          -∗ £ (S (num_later_per_step ns))
                          ={∅}▷=∗^(S $ num_later_per_step ns) |={∅,E}=>
                 state_interp_fun (S ns) σ'
                 ∗ self Φ E β
                 ∗ [∗ list] i ↦ ef ∈ en, self fork_post ⊤ ef)))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    intros ?????? H ?; simpl.
    f_equiv; first solve_proper.
    f_equiv.
    do 2 (f_equiv; intros ?).
    f_equiv.
    solve_proper_prepare.
    rewrite H.
    f_equiv.
  Qed.
  Next Obligation.
    intros ?????? [] ?; simpl.
    f_equiv; first solve_proper.
    f_equiv.
    f_equiv; intros ?.
    f_equiv; intros p.
    do 3 f_equiv.
    do 3 (f_equiv; intros ?).
    do 5 f_equiv.
    induction (num_later_per_step p).
    - solve_proper.
    - solve_proper.
  Qed.

  #[local] Instance wp_pre_contractive s : Contractive (wp_pre s).
  Proof.
    unfold wp_pre.
    intros m s1 s2 Hs Φ1 E1 a'; simpl.
    do 20 (f_contractive || f_equiv).
    induction num_later_per_step as [| k IH]; simpl.
    - solve_contractive.
    - rewrite -IH.
      solve_contractive.
  Qed.

  Definition wp α s E Φ := fixpoint (wp_pre s) Φ E α.

  Lemma wp_unfold  α E' s Φ :
    wp α s E' Φ ≡
       ((∃ αv, IT_to_V α ≡ Some αv ∧ |={E'}=> Φ αv)
        ∨ (IT_to_V α ≡ None
           ∧ ∀ σ ns, state_interp_fun ns σ
                  ={E',∅}=∗ ((∃ α' σ' en, internal_step α σ α' σ' en)
                             ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))
                  ∧ (∀ σ' β en, internal_step α σ β σ' en
                                -∗ £ (S (num_later_per_step ns))
                                ={∅}▷=∗^(S $ num_later_per_step ns) |={∅,E'}=>
                       state_interp_fun (S ns) σ'
                       ∗ wp β s E' Φ
                       ∗ [∗ list] i ↦ ef ∈ en, wp ef s ⊤ fork_post)))%I.
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
    f_equiv. f_equiv.
    f_equiv; intros ?.
    f_equiv.
    f_equiv.
    f_equiv; first solve_proper.
    do 3 (f_equiv; intros ?).
    f_equiv; first solve_proper.
    f_equiv.
    induction num_later_per_step as [| k IH']; simpl.
    - f_equiv.
      f_contractive.
      do 4 f_equiv.
      + apply IH; eauto.
        eapply dist_le; [apply Hp|lia].
      + do 3 f_equiv.
        unfold wp.
        do 3 f_equiv.
        apply fixpoint_ne.
        solve_proper.
    - f_equiv.
      f_equiv.
      f_equiv.
      apply IH'.
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
    iIntros (σ ns) "Hs". iMod "H" as "H".
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
      iSplit; first by eauto. iIntros (σ ns) "Hs".
      iMod ("H" with "Hs") as "[$ H]".
      iModIntro. iIntros (σ' β en) "Hst Hlc".
      iMod ("H" with "Hst Hlc") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iInduction (num_later_per_step) as [| k IH] "G".
      + iMod "H" as "[$ [H G]]".
        iModIntro.
        iSplitL "H H2".
        * by iApply ("IH" with "H").
        * iFrame.
      + iMod "H" as "H".
        iModIntro.
        iNext.
        iApply ("G" with "H1 H2 H").
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
    iIntros (σ ns) "Hs".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl". iSplit.
    - iLeft. iExists α,σ,[]. iLeft. eauto.
    - iIntros (σ' β en) "Hst Hlc". rewrite internal_step_tick.
      iDestruct "Hst" as "[#Hb [#Hs' #Hen]]".
      iRewrite "Hs'" in "Hs".
      iClear "Hs'".
      iSimpl.
      iModIntro.
      iNext.
      iRewrite - "Hb" in "H".
      iClear "Hb".
      iInduction num_later_per_step as [| k IH] "G".
      + iMod (state_interp_fun_mono with "Hs") as "Hs".
        iModIntro.
        iFrame "H".
        iAssert (⌜en = []⌝)%I as "->".
        {
          destruct en; first done.
          iExFalso.
          iPoseProof (list_equivI with "Hen") as "Hen'".
          iSpecialize ("Hen'" $! 0).
          by iPoseProof (option_equivI with "Hen'") as "Hen''".
        }
        iSimpl.
        iFrame "Hs".
        iMod "Hcl" as "_".
        iModIntro. done.
      + iDestruct "Hlc" as "[Hlc1 Hlc2]".
        iApply ("G" with "H Hs Hcl Hlc2").
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

  Local Definition wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s {{ Φ }})%I.

  Local Instance wptp_ne s : NonExpansive2 (wptp s).
  Proof.
    intros k x1 x2 Hx Φ1 Φ2 HΦ.
    rewrite /wptp.
    apply big_sepL2_ne_2; [done | done |].
    solve_proper.
  Qed.

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
                                 ∗ wptp s en (replicate (length en) fork_post) ))
    -∗ WP (Vis op x k) @ s;E1 {{ Φ }}.
  Proof.
    intros op x k.
    iIntros "H".
    rewrite (wp_unfold (Vis _ _ _)).
    iRight. iSplit.
    { iPureIntro. apply IT_to_V_Vis. }
    iIntros (fs ns) "Hgst".
    destruct (gState_decomp i fs) as [σ0 rest] eqn:Hdecomp.
    assert (fs ≡ gState_recomp rest σ0) as Hfs.
    { symmetry. apply gState_recomp_decomp.
      by rewrite Hdecomp. }
    iMod "H" as (σ σ' β en) "[Hlst H]".
    (* XXX: fixme, proper typeclass is not picked *)
    iAssert (state_interp_fun ns fs
               ≡ state_interp_fun ns (gState_recomp rest σ0))%I as "HEQ".
    {
      iApply f_equivI.
      rewrite Hfs.
      done.
    }
    iAssert (σ0 ≡ σ)%I with "[Hlst Hgst]" as "#Hss".
    {
      iRewrite "HEQ" in "Hgst". iClear "HEQ".
      iDestruct (state_interp_fun_decomp with "Hgst") as "[_ Hgst]".
      iApply (state_interp_has_state_idx_agree with "Hgst Hlst").
    }
    iDestruct ("H" $! rest) as "[Hreify H]".
    iRewrite -"Hss" in "Hreify".
    iEval (rewrite -Hfs) in "Hreify".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hcl2".
    iSplit.
    {
      (* it is safe *)
      iLeft.
      iExists β, (gState_recomp rest σ'), en. iRight.
      iExists op, x, k; eauto.
    }
    iIntros (fs' α0 en0) "Hst Hlc". rewrite internal_step_vis.
    iAssert (gState_recomp rest σ' ≡ fs' ∧ Tick β ≡ Tick α0 ∧ en ≡ en0)%I
      with "[Hreify Hst]" as "[Hst [Hb Hen]]".
    {
      iRewrite "Hreify" in "Hst".
      do 2 rewrite prod_equivI; simpl.
      iDestruct "Hst" as "(Hst & G)".
      iFrame "G".
      done.
    }
    iRewrite "HEQ" in "Hgst". iClear "HEQ".
    iDestruct (state_interp_fun_decomp with "Hgst") as "[Hrest Hgst]".
    iMod (state_interp_has_state_idx_update i σ' with "Hgst Hlst") as "[Hgst Hlst]".
    iDestruct (state_interp_fun_decomp with "[$Hrest $Hgst]") as "Hgst".
    iMod (state_interp_fun_mono with "Hgst") as "Hgst".
    iModIntro. iNext. iModIntro.
    iAssert (state_interp_fun (S ns) fs')%I with "[Hgst Hst]" as "Hgst".
    {
      iAssert (state_interp_fun (S ns) (gState_recomp rest σ')
                 ≡ state_interp_fun (S ns) fs')%I with "[Hst]" as "HEQ".
      { by iApply f_equivI. }
      iRewrite -"HEQ".
      done.
    }
    iInduction num_later_per_step as [| p IH] "J".
    - iFrame "Hgst".
      iMod "Hcl2" as "_".
      iMod ("H" with "Hlc Hlst") as "[H1 H2]".
      iModIntro.
      iRewrite -"Hb".
      iFrame "H1".
      unfold wptp.
      rewrite big_sepL2_replicate_r; last done.
      iApply (internal_eq_rewrite with "Hen");
        last iExact "H2".
      intros m t1 t2 H.
      apply big_opL_ne_2; first done.
      solve_proper.
    - iModIntro.
      iNext.
      iDestruct "Hlc" as "[Hlc1 Hlc2]".
      iApply ("J" with "H Hcl2 Hlc2 Hb Hen Hlst Hgst").
  Qed.

  Lemma wp_reify  E1 s Φ i (lop : opid (sReifier_ops (rs !!! i)))
    x k σ σ' β en :
    let op : opid F := (existT i lop) in
    (∀ rest, reify (Vis op x k)  (gState_recomp rest σ) ≡ (gState_recomp rest σ', Tick β, en)) →
    has_state_idx i σ
    -∗ ▷ (£ 1 -∗ has_state_idx i σ'
          -∗ WP β @ s;E1 {{ Φ }}
                      ∗ wptp s en (replicate (length en) fork_post))
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
    iIntros (σ ns) "Hσ". iApply fupd_mask_intro; first set_solver.
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
      iSplit; first by eauto. iIntros (σ ns) "Hs".
      iMod ("H" with "Hs") as "[Hs H]".
      iModIntro. iSplit.
      { iDestruct "Hs" as "[$ | Hs]".
        iRight. iDestruct "Hs" as (e) "[He %]".
        iExists e; iSplit; eauto. }
      iIntros (σ' β en) "Hst Hlc".
      iMod ("H" with "Hst Hlc") as "H".
      iModIntro. iNext.
      iMod "H" as "H". iModIntro.
      iInduction num_later_per_step as [| p IH] "J".
      + iMod "H" as "[$ [G1 G2]]".
        iModIntro.
        iSplitL "IH G1".
        * by iApply ("IH" with "G1").
        * iInduction en as [| en] "IH'"; first done.
          rewrite !big_opL_cons.
          iDestruct "G2" as "[G2 G3]".
          iSplitL "G2".
          -- by iApply ("IH" with "G2").
          -- by iApply ("IH'" with "[$H1] [$Hs]").
      + iMod "H" as "H".
        iModIntro.
        iNext.
        iApply ("J" with "H1 Hs H").
  Qed.

  (** "preservation" statements *)
  Lemma wp_internal_step_preservation' i α σ β σ' en s Ψ :
    ⊢ internal_step α σ β σ' en
      -∗ state_interp_fun i σ
      -∗ WP α @ s {{ Ψ }}
      -∗ £ (S (num_later_per_step i))
      ={⊤,∅}=∗ |={∅}▷=>^(S $ num_later_per_step i) |={∅,⊤}=>
          state_interp_fun (S i) σ'
          ∗ WP β @ s {{ Ψ }}
          ∗ [∗ list] ef ∈ en, WP ef @ s {{ fork_post }}.
  Proof.
    iIntros "Hstep Hs H Hlc".
    rewrite (wp_unfold α). iDestruct "H" as "[H|[Ha H]]".
    - iExFalso. iDestruct "H" as (αv) "[H _]".
      iApply (internal_step_ITV with "H Hstep").
    - iSpecialize ("H" with "Hs"). iDestruct "H" as "[_ H]".
      iMod "H" as "H".
      iMod ("H" with "Hstep Hlc") as "H".
      iModIntro. iModIntro.
      iNext.
      iMod "H" as "H".
      iModIntro.
      iInduction num_later_per_step as [| p IH] "J".
      + iMod "H" as "[H1 [H2 H3]]".
        iFrame "H1 H2 H3".
        by iModIntro.
      + iMod "H" as "H".
        iModIntro.
        iNext.
        iApply ("J" with "Ha H").
  Qed.

  Lemma wp_internal_step_preservation i α σ β σ' en s Ψ :
    ⊢ internal_step α σ β σ' en
      -∗ aux_interp_fun i
      -∗ state_interp σ
      -∗ WP α @ s {{ Ψ }}
      -∗ £ (S (num_later_per_step i))
      ={⊤,∅}=∗ |={∅}▷=>^(S $ num_later_per_step i) |={∅,⊤}=>
          aux_interp_fun (S i)
          ∗ state_interp σ'
          ∗ WP β @ s {{ Ψ }}
          ∗ [∗ list] ef ∈ en, WP ef @ s {{ fork_post }}.
  Proof.
    iIntros "Hstep Haux Hs H Hlc".
    iDestruct (state_interp_fun_decomp with "[$Hs $Haux]") as "Hs".
    iMod (wp_internal_step_preservation' with "Hstep Hs H Hlc") as "H".
    iModIntro.
    iInduction num_later_per_step as [| p IH] "J".
    - iMod "H" as "H".
      iModIntro.
      iNext.
      iMod "H" as "H".
      iModIntro.
      iMod "H" as "(H1 & H2 & H3)".
      iModIntro.
      iFrame "H2 H3".
      iApply (state_interp_fun_decomp with "H1").
    - iMod "H" as "H".
      iModIntro.
      iNext.
      iApply "J".
      iApply "H".
  Qed.

  Local Lemma wptp_internal_step_preservation' αs σ βs σ' ns s Φs :
    tp_internal_step αs σ βs σ'
    -∗ state_interp_fun ns σ
    -∗ £ (S (num_later_per_step ns))
    -∗ wptp s αs Φs
    -∗ ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_later_per_step ns) |={∅,⊤}=>
          state_interp_fun (S ns) σ' ∗
            wptp s βs (Φs ++ replicate nt' fork_post).
  Proof.
    iIntros "Hstep Hσ Hcred Ht".
    iDestruct "Hstep" as (α1 α2 γ γ' en) "(HEQ1 & HEQ2 & Hstep)".
    iExists (length en).
    iRewrite "HEQ1" in "Ht".
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[H1 Ht]".
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht H2]".
    iMod (wp_internal_step_preservation' with "Hstep Hσ Ht Hcred") as "H". iModIntro.
    iApply (step_fupdN_wand with "H"). iIntros ">($ & He2 & Hefs) !>".
    rewrite -(assoc_L app) -app_comm_cons.
    iRewrite "HEQ2".
    iFrame "H1 He2 H2".
    rewrite big_sepL2_replicate_r; done.
  Qed.

  Local Lemma wptp_internal_step_preservation αs σ βs σ' ns s Φs :
    tp_internal_step αs σ βs σ'
    -∗ aux_interp_fun ns
    -∗ state_interp σ
    -∗ £ (S (num_later_per_step ns))
    -∗ wptp s αs Φs
    -∗ ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_later_per_step ns) |={∅,⊤}=>
          aux_interp_fun (S ns) ∗
          state_interp σ' ∗
            wptp s βs (Φs ++ replicate nt' fork_post).
  Proof.
    iIntros "Hstep Hσ Haux Hcred Ht".
    iDestruct (state_interp_fun_decomp with "[$Hσ $Haux]") as "Hσ".
    iDestruct (wptp_internal_step_preservation' with "Hstep Hσ Hcred Ht") as (nt) "H".
    iExists nt.
    iMod "H". iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros ">(H1 & H2)".
    iFrame "H2".
    iDestruct (state_interp_fun_decomp with "H1") as "(Hσ & Haux)".
    by iFrame.
  Qed.

  Local Fixpoint steps_sum (num_later_per_step : nat → nat) (start ns : nat) : nat :=
    match ns with
    | O => 0
    | S ns =>
        S $ num_later_per_step start + steps_sum num_later_per_step (S start) ns
    end.

  Local Lemma wptp_internal_steps_preservation' αs σ βs σ' m ns s Φs :
  tp_internal_steps αs σ βs σ' m
  -∗ state_interp_fun ns σ
  -∗ £ (steps_sum num_later_per_step ns m) -∗
  wptp s αs Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_later_per_step ns m) |={∅,⊤}=> ∃ nt',
    state_interp_fun (m + ns) σ'
    ∗ wptp s βs (Φs ++ replicate nt' fork_post).
  Proof.
    revert αs σ βs σ' ns Φs.
    induction m as [| m IH];
      intros αs σ βs σ' ns Φs;
      iIntros "Hsteps Hσ HCred H".
    - rewrite tp_internal_steps_0.
      iDestruct "Hsteps" as "(HEQ1 & HEQ2)".
      iRewrite "HEQ1" in "H".
      iRewrite "HEQ2" in "Hσ".
      iExists 0.
      iSimpl.
      rewrite app_nil_r.
      iFrame "Hσ H".
      by iApply fupd_mask_subseteq.
    - rewrite tp_internal_steps_S.
      iDestruct "Hsteps" as (γ σ'') "(Hstep & Hsteps)".
      iSimpl in "HCred".
      iDestruct "HCred" as "(HCred1 & HCred2 & HCred3)".
      iCombine "HCred1 HCred2" as "HCred1".
      iDestruct (wptp_internal_step_preservation' with "Hstep Hσ HCred1 H") as (nt') ">H".
      specialize (IH γ σ'' βs σ' (S ns) (Φs ++ replicate nt' fork_post)).
      iSimpl.
      iModIntro.
      iApply step_fupdN_S_fupd.
      rewrite /= step_fupdN_add.
      iMod "H".
      iApply step_fupdN_S_fupd.
      iSimpl.
      iModIntro.
      iNext.
      iMod "H".
      iModIntro.
      iApply (step_fupdN_wand with "H").
      iIntros ">(H1 & H2)".
      iDestruct (IH with "Hsteps H1 HCred3 H2") as ">IH".
      iModIntro.
      iApply (step_fupdN_wand with "IH"). iIntros ">IH".
      iDestruct "IH" as (nt'') "[??]".
      rewrite -app_assoc -replicate_add.
      rewrite Nat.add_succ_r.
      iExists _.
      iFrame.
      by iApply fupd_mask_subseteq.
  Qed.

  Local Lemma wptp_internal_steps_preservation αs σ βs σ' m ns s Φs :
  tp_internal_steps αs σ βs σ' m
  -∗ aux_interp_fun ns
  -∗ state_interp σ
  -∗ £ (steps_sum num_later_per_step ns m) -∗
  wptp s αs Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_later_per_step ns m) |={∅,⊤}=> ∃ nt',
    aux_interp_fun (m + ns)
    ∗ state_interp σ'
    ∗ wptp s βs (Φs ++ replicate nt' fork_post).
  Proof.
    iIntros "Hstep Haux Hσ HCred H".
    iDestruct (state_interp_fun_decomp with "[$Hσ $Haux]") as "Hσ".
    iDestruct (wptp_internal_steps_preservation' with "Hstep Hσ HCred H") as ">H".
    iModIntro.
    iApply (step_fupdN_wand with "H").
    iIntros ">(%nt & H1 & H2)".
    iExists nt.
    iDestruct (state_interp_fun_decomp with "H1") as "(Hσ & Haux)".
    iFrame "H2 Hσ Haux".
    done.
  Qed.

  Lemma wp_external_step_preservation α σ β σ' en i s Ψ :
    external_step α σ β σ' en →
    state_interp_fun i σ
    ∗ WP α @ s {{ Ψ }}
    ∗ £ (S (num_later_per_step i))
    ={⊤,∅}=∗ |={∅}▷=>^(S $ num_later_per_step i) |={∅,⊤}=>
          state_interp_fun (S i) σ'
          ∗ WP β @ s {{ Ψ }}
          ∗ ([∗ list] ef ∈ en, WP ef @ s {{ fork_post }}).
  Proof.
    iIntros (Hst) "[Hs [HIC HCred]]".
    iAssert (internal_step α σ β σ' en) as "Hst".
    { by iApply external_step_internal_step. }
    iApply (wp_internal_step_preservation' with "Hst Hs HIC HCred").
  Qed.

  Lemma wp_tp_external_step_preservation αs σ βs σ' s Ψs ns :
    tp_external_step αs σ βs σ' →
    state_interp_fun ns σ
    ∗ £ (S (num_later_per_step ns))
    ∗ wptp s αs Ψs
    -∗ ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_later_per_step ns) |={∅,⊤}=>
          state_interp_fun (S ns) σ'
          ∗ wptp s βs (Ψs ++ replicate nt' fork_post).
  Proof.
    iIntros (Hst) "[Hs [HIC HCred]]".
    iAssert (tp_internal_step αs σ βs σ') as "Hst".
    { by iApply tp_external_step_tp_internal_step. }
    iApply (wptp_internal_step_preservation' with "Hst Hs HIC HCred").
  Qed.

  Lemma wp_tp_external_steps_preservation αs σ βs σ' s Ψs m ns :
    tp_external_steps αs σ βs σ' m →
    state_interp_fun ns σ
    ∗ £ (steps_sum num_later_per_step ns m)
    ∗ wptp s αs Ψs
    ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_later_per_step ns m) |={∅,⊤}=> ∃ nt',
    state_interp_fun (m + ns) σ'
    ∗ wptp s βs (Ψs ++ replicate nt' fork_post).
  Proof.
    iIntros (Hst) "[Hs [HIC HCred]]".
    iAssert (tp_internal_steps αs σ βs σ' m) as "Hst".
    { by iApply tp_external_steps_tp_internal_steps. }
    iApply (wptp_internal_steps_preservation' with "Hst Hs HIC HCred").
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

  Definition not_stuck α σ s : iProp := (⌜is_Some (IT_to_V α)⌝
                                 ∨ (∃ β σ' l, internal_step α σ β σ' l)
                                 ∨ (∃ e, α ≡ Err e ∧ ⌜s e⌝))%I.

  Lemma wp_not_stuck α σ s i Ψ :
    state_interp_fun i σ
    ∗ WP α @ s {{ Ψ }}
    ={⊤, ∅}=∗ not_stuck α σ s.
  Proof.
    iIntros "[Hs H]".
    rewrite wp_unfold.
    iDestruct "H" as "[[% [H1 H2]] | [H1 H2]]".
    - iLeft.
      iMod (fupd_mask_subseteq ∅); first set_solver. iModIntro.
      destruct (IT_to_V α) as [αv'|].
      + by rewrite is_Some_alt.
      + iExFalso. iApply (option_equivI with "H1").
    - iMod ("H2" $! σ i with "Hs") as "[[H2 | H2] _]".
      + iRight. iLeft.
        by iModIntro.
      + iRight. iRight.
        by iModIntro.
  Qed.

  Lemma wp_internal_step_progress α σ β σ' l s i Ψ :
    internal_step α σ β σ' l
    ∗ state_interp_fun i σ
    ∗ WP α @ s {{ Ψ }}
    ∗ £ (S (num_later_per_step i))
    ={⊤,∅}=∗ |={∅}▷=>^(S (num_later_per_step i)) |={∅}=> not_stuck β σ' s.
  Proof.
    iIntros "(Hstep & Hs & H & Hcred)".
    iMod (wp_internal_step_preservation' with "Hstep Hs H Hcred") as "J".
    iModIntro.
    iApply (step_fupdN_wand with "J").
    iIntros ">(J1 & H & J2)".
    iApply (wp_not_stuck with "[$J1 $H]").
  Qed.

  Lemma wp_tp_internal_steps_progress αs σ e βs σ' m s ns Ψs :
    e ∈ βs ->
    tp_internal_steps αs σ βs σ' m
    ∗ state_interp_fun ns σ
    ∗ wptp s αs Ψs
    ∗ £ (steps_sum num_later_per_step ns m)
    ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_later_per_step ns m) |={∅}=> not_stuck e σ' s.
  Proof.
    iIntros (HIn) "(Hstep & Hs & H & Hcred)".
    iDestruct (state_interp_fun_decomp with "Hs") as "[Hs Haux]".
    iMod (wptp_internal_steps_preservation with "Hstep Hs Haux Hcred H") as "J".
    iModIntro.
    iApply (step_fupdN_wand with "J").
    iIntros ">(%nt & J1 & J2 & J3)".
    eapply elem_of_list_lookup in HIn as [i Hlook].
    destruct ((Ψs ++ replicate nt fork_post) !! i) as [Φ|] eqn: Hlook2; last first.
    {
      rewrite /wptp big_sepL2_alt. iDestruct "J3" as "[%Hlen J3]". exfalso.
      eapply lookup_lt_Some in Hlook. rewrite Hlen in Hlook.
      eapply lookup_lt_is_Some_2 in Hlook. rewrite Hlook2 in Hlook.
      destruct Hlook as [? ?]. naive_solver.
    }
    rewrite /wptp.
    iDestruct (big_sepL2_lookup with "J3") as "Ht"; [done..|].
    iDestruct (state_interp_fun_decomp with "[$J1 $J2]") as "Hs".
    by iApply (wp_not_stuck with "[$Ht $Hs]").
  Qed.

  Lemma wp_internal_steps_val α σ βv σ' l i s Ψ `{!NonExpansive Ψ} :
    internal_step α σ (IT_of_V βv) σ' l
    ∗ state_interp_fun i σ
    ∗ WP α @ s {{ Ψ }}
    ∗ £ (S (num_later_per_step i))
    ={⊤,∅}=∗ |={∅}▷=>^(S (num_later_per_step i)) |={∅}=> Ψ βv.
  Proof.
    iIntros "(Hstep & Hs & H & Hcred)".
    iDestruct (wp_internal_step_preservation' with "Hstep Hs H Hcred") as "J".
    iMod "J".
    iModIntro.
    iApply (step_fupdN_wand with "J").
    iIntros ">(_ & H & _)".
    iPoseProof (wp_val_inv with "H") as "H".
    iMod "H".
    iFrame "H".
    iMod (fupd_mask_subseteq ∅); first set_solver. by iModIntro.
  Qed.

  Lemma wptp_postconditions (Φs : list (ITV -d> iProp))
    (HΦ : Forall (λ f, NonExpansive f) Φs)
    s m es1 es2 σ1 ns σ2 :
    tp_internal_steps es1 σ1 es2 σ2 m
    -∗ state_interp_fun ns σ1
    -∗ £ (steps_sum num_later_per_step ns m)
    -∗ wptp s es1 Φs
    ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_later_per_step ns m) |={∅,⊤}=> ∃ nt',
    state_interp_fun (m + ns) σ2
    ∗ [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (IT_to_V e).
  Proof.
    iIntros "Hstep Hσ Hcred He".
    iMod (wptp_internal_steps_preservation' with "Hstep Hσ Hcred He") as "Hwp".
    iModIntro. iApply (step_fupdN_wand with "Hwp").
    iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
    iExists _. iFrame "Hσ".
    iApply big_sepL2_fupd.
    iApply (big_sepL2_impl with "Ht").
    iIntros "!#" (k e Φ ? HH) "Hwp".
    destruct (IT_to_V e) as [v2|] eqn:He2'.
    - iMod (wp_val_inv _ v2 with "Hwp") as "J".
      + assert (Forall (λ f, NonExpansive f) (replicate nt' fork_post)) as GG.
        { apply Forall_replicate; apply fork_post_ne. }
        apply (Forall_lookup_1 (λ f, NonExpansive f)
                 (Φs ++ replicate nt' fork_post) k Φ); last done.
        apply Forall_app.
        split; done.
      + apply IT_of_to_V'. by rewrite He2'.
      + rewrite He2' /=.
        by iFrame "J".
    - by rewrite He2'.
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

Section weakestpre_ectx_indep.
  Context {n : nat} {A} `{!Cofe A}.
  Context (rs : (gReifiers NotCtxDep n)).
  Notation F := (sReifier_ops (gReifiers_sReifier (n := n) rs)).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state).
  Notation stateO := (stateF rs ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Let of_idx := (of_idx rs IT).
  Notation reify := (reify rs).
  Notation internal_step := (internal_step rs).
  Notation internal_steps := (internal_steps rs).
  Notation tp_internal_step := (tp_internal_step rs).
  Notation tp_internal_steps := (tp_internal_steps rs).
  Notation external_step := (external_step rs).
  Notation external_steps := (external_steps rs).
  Notation tp_external_step := (tp_external_step rs).
  Notation tp_external_steps := (tp_external_steps rs).

  Context `{!gitreeGS_gen rs A Σ}.

  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Lemma wp_reify_idx_ctx_indep
    E1 E2 s Φ i
    (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid F := (existT i lop) in
    forall (x : Ins (F op) ♯ IT)
      (k : Outs (F op) ♯ IT -n> laterO IT),
    (|={E1,E2}=>  ∃ σ y σ' β l,
       has_state_idx i σ
       ∗ sReifier_re (rs !!! i) lop (x, σ) ≡ Some (y, σ', l)
       ∗ k y ≡ Next β
       ∗ ▷ (£ 1 -∗ has_state_idx i σ'
            ={E2,E1}=∗ WP@{rs} β @ s; E1 {{ Φ }}
               ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post)))
       -∗ WP@{rs} (Vis op x k) @ s; E1 {{ Φ }}.
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
    { pose proof (@gReifiers_re_idx n NotCtxDep i rs IT) as J.
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

  Lemma wp_subreify_ctx_indep'
    E1 E2 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR)) (x : Ins (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT) :
    (|={E1,E2}=> ∃ σ y σ' β l,
       has_substate σ
       ∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
       ∗ k (subEff_outs y) ≡ Next β
       ∗ ▷ (£ 1 -∗ has_substate σ'
         ={E2,E1}=∗ wp rs β s E1 Φ
        ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post)))
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

  Lemma wp_subreify_ctx_indep
    E1 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ'
          -∗ wp rs β s E1 Φ
           ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post))
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

End weakestpre_ectx_indep.

Section weakestpre_ectx_dep.
  Context {n : nat} {A} `{!Cofe A}.
  Context (rs : (gReifiers CtxDep n)).
  Notation F := (sReifier_ops (gReifiers_sReifier (n := n) rs)).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state).
  Notation stateO := (stateF rs ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Let of_idx := (of_idx rs IT).
  Notation reify := (reify rs).
  Notation internal_step := (internal_step rs).
  Notation internal_steps := (internal_steps rs).
  Notation tp_internal_step := (tp_internal_step rs).
  Notation tp_internal_steps := (tp_internal_steps rs).
  Notation external_step := (external_step rs).
  Notation external_steps := (external_steps rs).
  Notation tp_external_step := (tp_external_step rs).
  Notation tp_external_steps := (tp_external_steps rs).

  Context `{!gitreeGS_gen rs A Σ}.

  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Lemma wp_reify_idx_ctx_dep
    E1 E2 s Φ i
    (lop : opid (sReifier_ops (rs !!! i))) :
    let op : opid F := (existT i lop) in
    forall (x : Ins (F op) ♯ IT)
      (k : Outs (F op) ♯ IT -n> laterO IT),
    (|={E1,E2}=>
       ∃ σ y σ' β l,
       has_state_idx i σ
       ∗ sReifier_re (rs !!! i) lop (x, σ, k) ≡ Some (y, σ', l)
       ∗ y ≡ Next β
       ∗ ▷ (£ 1 -∗ has_state_idx i σ'
            ={E2,E1}=∗
            wp rs β s E1 Φ
            ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post)))
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

  Lemma wp_subreify_ctx_dep'
    E1 E2 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR)) (x : Ins (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT) :
    (|={E1,E2}=> ∃ σ y σ' β l,
       has_substate σ
       ∗ sReifier_re sR op (x, σ, (k ◎ subEff_outs)) ≡ Some (y, σ', l)
       ∗ y ≡ Next β
       ∗ ▷ (£ 1 -∗ has_substate σ'
            ={E2,E1}=∗ wp rs β s E1 Φ
                     ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post)))
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

  Lemma wp_subreify_ctx_dep
    E1 s Φ sR `{!subReifier sR rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT) (y : laterO IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l :
    sReifier_re sR op (x, σ, (k ◎ subEff_outs)) ≡ Some (y, σ', l) →
    y ≡ Next β →
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ' -∗ wp rs β s E1 Φ
      ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post))
    -∗ wp rs (Vis (subEff_opid op) (subEff_ins x) k) s E1 Φ.
  Proof.
    intros HSR Hk.
    iIntros "Hlst H".
    iApply (wp_reify with "Hlst H").
    intros rest.
    rewrite Tick_eq. rewrite -Hk.
    rewrite reify_vis_eq_ctx_dep //.
    pose proof (@subReifier_reify n CtxDep sR rs _
                  (IT) _ op x y (k ◎ subEff_outs) σ σ' rest) as H'.
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

End weakestpre_ectx_dep.

Section weakestpre_lifting.
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

  Global Instance subEffCtxIndep a (rs : gReifiers a n)
    sR
    `{!subReifier (sReifier_NotCtxDep_min sR a) rs}
    : subEff (sReifier_ops sR) (F rs).
  Proof.
    refine subReifier_subEff.
  Defined.

  Lemma wp_subreify_ctx_indep_lift (rs : gReifiers CtxDep n)
    `{gitreeGS_gen n _ rs A Σ}
    E1 s Φ sR
    `{!subReifier (sReifier_NotCtxDep_CtxDep sR) rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs)
    (y : Outs (sReifier_ops sR op) ♯ IT rs)
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β l :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ'
          -∗ wp rs β s E1 Φ
           ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post))
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
    `{gitreeGS_gen n _ rs A Σ}
    E1 s Φ sR
    `{!subReifier (sReifier_NotCtxDep_min sR a) rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT rs)
    (y : Outs (sReifier_ops sR op) ♯ IT rs)
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs))
    (σ σ' : sReifier_state sR ♯ IT rs) β l :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ'
          -∗ wp rs β s E1 Φ
           ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post))
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
    `{gitreeGS_gen n _ rs A Σ}
    E1 E2 s Φ sR
    `{!subReifier (sReifier_NotCtxDep_min sR a) rs}
    (op : opid (sReifier_ops sR)) (x : Ins (sReifier_ops sR op) ♯ (IT rs))
    (k : Outs (F rs (subEff_opid op)) ♯ IT rs -n> laterO (IT rs)) :
    (|={E1,E2}=> ∃ σ y σ' β l,
       has_substate σ ∗
         sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
       ∗ k (subEff_outs y) ≡ Next β
       ∗ ▷ (£ 1 -∗ has_substate σ'
            ={E2,E1}=∗ wp rs β s E1 Φ
                     ∗ wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post)))
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

End weakestpre_lifting.

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

  Context `{!gitreeGS_gen rs A Σ}.
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
      {
        apply (IT_hom_val_inv _ f). rewrite Hfa.
        done.
      }
      assert (IntoVal α αv).
      { apply IT_of_to_V'. by rewrite Ha. }
      rewrite wp_val_inv.
      iApply wp_val_inv.
      rewrite IT_of_to_V'; last by rewrite -Ha.
      rewrite IT_of_to_V'; last by rewrite -Hfa.
      by iApply fupd_wp.
    - iRight. iSplit; eauto.
      iIntros (σ ns) "Hs".
      rewrite wp_unfold.
      iDestruct "H" as "[H | H]".
      + iDestruct "H" as (αv) "[Hav H]".
        iPoseProof (IT_of_to_V with "Hav") as "Hav".
        iMod "H" as "H". rewrite wp_unfold.
        iDestruct "H" as "[H|H]".
        {
          iExFalso. iDestruct "H" as (βv) "[H _]".
          iRewrite "Hav" in "H". rewrite Hfa.
          iApply (option_equivI with "H").
        }
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
            iRewrite "Herr". rewrite hom_err//.
        }
        iIntros (σ' β l) "Hst".
        rewrite {1}internal_step_hom_inv. iDestruct "Hst" as "[%Ha | [_ Hst]]".
        {
          destruct Ha as [αv Ha]. rewrite Ha.
          iExFalso.
          iApply (option_equivI with "Hav").
        }
        iDestruct "Hst" as (α') "[Hst Hb]".
        iIntros "Hlc".
        iSimpl.
        iSimpl in "H".
        iMod ("H" with "Hst Hlc") as "H". iModIntro.
        iNext. iMod "H" as "H". iModIntro.
        iApply (step_fupdN_wand with "H").
        iIntros ">H".
        iModIntro.
        iDestruct "H" as "[$ [H1 H2]]".
        iRewrite "Hb".
        iSplitR "H2"; last done.
        by iApply "IH".
  Qed.

End weakestpre_bind.

Arguments wp {_ _} rs {_ _ _ _} α s E Φ.
Arguments has_full_state {n _ _ _ _ _ _} σ.
Arguments has_state_idx {n _ _ _ _ _ _} i σ.
Arguments has_substate {n _ _ _ _ _ _ _ _} σ.
Arguments stateG {n _} rs A {_} Σ.
Arguments statePreG {n _} rs A {_} Σ.
Arguments stateΣ {n _} rs A {_}.

Lemma wp_adequacy_tp (num_later_per_step : nat → nat)
  n a (rs : gReifiers a n)
  {A} `{!Cofe A}
  Σ `{!invGpreS Σ} `{!statePreG rs A Σ}
  α σ β σ' (s : stuckness) k ψ :
  let rg := gReifiers_sReifier rs in
  let F := sReifier_ops rg in
  let IT := IT F A in
  let ITV := ITV F A in
  (∀ `{H1 : !invGS_gen HasLc Σ} `{H2 : !stateG rs A Σ},
     (⊢@{iProp Σ} |={⊤}=> ∃
                            (state_interp_fun
                              : nat
                                → (gReifiers_state rs) ♯ IT
                                → iProp Σ)
                            (aux_interp_fun : nat → iProp Σ)
                            (fork_post : ITV -d> iProp Σ)
                            fork_post_ne
                            (Φs : list (ITV -d> iProp Σ))
                            state_interp_fun_mono
                            state_interp_fun_ne
                            state_interp_fun_decomp,
        let _ : gitreeGS_gen rs A Σ :=
          GitreeG rs A Σ H1 H2
            state_interp_fun aux_interp_fun
            fork_post
            fork_post_ne
            num_later_per_step
            state_interp_fun_mono
            state_interp_fun_ne
            state_interp_fun_decomp
        in
        tp_internal_steps (A := A) (gReifiers_sReifier rs) α σ β σ' k
        ∗ state_interp_fun 0 σ
        ∗ wptp rs s α Φs
        ∗ (state_interp_fun k σ' -∗ |={⊤,∅}=> ⌜ ψ ⌝))%I)
  → ψ.
Proof.
  intros rg F IT' ITV' Hprf.
  cut (⊢ ⌜ψ⌝ : iProp Σ)%I.
  { intros HH. eapply uPred.pure_soundness; eauto. }
  eapply (step_fupdN_soundness_lc _ (steps_sum num_later_per_step 0 k)
            (steps_sum num_later_per_step 0 k)).
  intros Hinv. iIntros "Hcred".
  iMod (new_state_interp σ) as (sg) "[Hs Hs2]".
  specialize (Hprf Hinv sg).
  iMod Hprf as (state_interp_fun aux_interp_fun
                  fork_post
                  fork_post_ne
                  ?
                  state_interp_fun_mono
                  state_interp_fun_ne
                  state_interp_fun_decomp)
                 "(Hstep & Hσ & Hwp & H)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_postconditions n a rs A _ Σ
          (GitreeG rs A Σ _ _
             state_interp_fun
             aux_interp_fun
             fork_post
             fork_post_ne
             num_later_per_step
             state_interp_fun_mono
             state_interp_fun_ne
             state_interp_fun_decomp) _ _ s k α β σ
          0 σ' with "Hstep Hσ Hcred Hwp") as "J".
  iModIntro.
  iApply (step_fupdN_wand with "J").
  iIntros "J".
  iEval (rewrite Nat.add_0_r) in "J".

Qed.

(* Lemma wp_safety cr Σ `{!invGpreS Σ} n a (rs : gReifiers a n) *)
(*   {A} `{!Cofe A} `{!statePreG rs A Σ} s l k *)
(*   (α β : IT (gReifiers_ops rs) A) (σ σ' : gReifiers_state rs ♯ IT (gReifiers_ops rs) A) : *)
(*   (∀ Σ P Q, @disjunction_property Σ P Q) → *)
(*   external_steps (gReifiers_sReifier rs) α σ β σ' l k → *)
(*   IT_to_V β ≡ None → *)
(*   (∀ `{H1 : !invGS_gen HasLc Σ} `{H2: !stateG rs A Σ}, *)
(*      ∃ Φ, NonExpansive Φ ∧ (£ cr ∗ has_full_state σ ⊢ WP@{rs} α @ s {{ Φ }})%I)  → *)
(*   ((∃ β1 σ1 l1, external_step (gReifiers_sReifier rs) β σ' β1 σ1 l1) *)
(*    ∨ (∃ e, β ≡ Err e ∧ s e)). *)
(* Proof. *)
(*   Opaque internal_step. *)
(*   intros Hdisj Hstep Hbv Hwp. *)
(*   cut (⊢@{iProp Σ} (∃ β1 σ1 l1, internal_step (gReifiers_sReifier rs) β σ' β1 σ1 l1) *)
(*         ∨ (∃ e, β ≡ Err e ∧ ⌜s e⌝))%I. *)
(*   { intros [Hprf | Hprf]%Hdisj. *)
(*     - left. *)
(*       apply (internal_step_safe_external_step _ (Σ:=Σ)). *)
(*       { apply Hdisj. } *)
(*       done. *)
(*     - right. *)
(*       destruct (IT_dont_confuse β) *)
(*         as [[e Ha] | [[m Ha] | [ [g Ha] | [[α' Ha]|[op [i [ko Ha]]]] ]]]. *)
(*       + exists e. split; eauto. *)
(*         eapply uPred.pure_soundness. *)
(*         iPoseProof (Hprf) as "H". *)
(*         iDestruct "H" as (e') "[He %Hs]". rewrite Ha. *)
(*         iPoseProof (Err_inj' with "He") as "%He". *)
(*         iPureIntro. rewrite He//. *)
(*       + exfalso. eapply uPred.pure_soundness. *)
(*         iPoseProof (Hprf) as "H". *)
(*         iDestruct "H" as (e') "[Ha Hs]". rewrite Ha. *)
(*         iApply (IT_ret_err_ne with "Ha"). *)
(*       + exfalso. eapply uPred.pure_soundness. *)
(*         iPoseProof (Hprf) as "H". *)
(*         iDestruct "H" as (e') "[Ha Hs]". rewrite Ha. *)
(*         iApply (IT_fun_err_ne with "Ha"). *)
(*       + exfalso. eapply uPred.pure_soundness. *)
(*         iPoseProof (Hprf) as "H". *)
(*         iDestruct "H" as (e') "[Ha Hs]". rewrite Ha. *)
(*         iApply (IT_tick_err_ne with "Ha"). *)
(*       + exfalso. eapply uPred.pure_soundness. *)
(*         iPoseProof (Hprf) as "H". *)
(*         iDestruct "H" as (e') "[Ha Hs]". rewrite Ha. *)
(*         iApply (IT_vis_err_ne with "Ha"). } *)
(*   eapply (step_fupdN_soundness_lc _ 0 (cr + (3*k+2))). *)
(*   intros Hinv. iIntros "[Hcr Hlc]". *)
(*   iMod (new_state_interp rs σ) as (sg) "[Hs Hs2]". *)
(*   destruct (Hwp Hinv sg) as (Φ & HΦ & Hprf'). *)
(*   iPoseProof (Hprf' with "[$Hs2 $Hcr]") as "Hic". *)
(*   iPoseProof (wp_external_steps_internal_safe with "[$Hs $Hic]") as "H". *)
(*   { eassumption. } *)
(*   iMod ("H" with "Hlc") as "[H | H]". *)
(*   { iDestruct "H" as (βv) "%Hbeta". *)
(*     exfalso. rewrite Hbeta  in Hbv. *)
(*     inversion Hbv. } *)
(*   iFrame "H". *)
(*   by iApply fupd_mask_intro_discard. *)
(* Qed. *)
