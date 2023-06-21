From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify.

Section sstep.
  Context (r : sReifier).
  Notation F := (sReifier_ops r).
  Notation stateF := (sReifier_state r).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Notation stateO := (stateF ♯ IT).
  Implicit Type op : opid F.
  Implicit Type α β : IT.
  Implicit Type σ : stateO.

  (** ** Reductions at the Prop level *)
  Inductive sstep : IT → stateO → IT → stateO → Prop :=
  | sstep_tick α β σ σ' :
    α ≡ Tick β →
    σ ≡ σ' →
    sstep α σ β σ'
  | sstep_reify α op i k β σ1 σ2 :
    α ≡ Vis op i k →
    reify r (Vis op i k) σ1 ≡ (σ2, Tick β) →
    sstep α σ1 β σ2.
  #[export] Instance sstep_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (iff)) sstep.
  Proof.
    intros α1 α2 Ha σ1 σ2 Hs β1 β2 Hb σ'1 σ'2 Hs'.
    simplify_eq/=. split.
    - induction 1.
      + eapply sstep_tick.
        ++ rewrite -Ha -Hb//.
        ++ rewrite -Hs' -Hs//.
      + eapply sstep_reify.
        ++ rewrite -Ha//.
        ++ rewrite -Hb -Hs' -Hs//.
    - induction 1.
      + eapply sstep_tick.
        ++ rewrite Ha Hb//.
        ++ rewrite Hs' Hs//.
      + eapply sstep_reify.
        ++ rewrite Ha//.
        ++ rewrite Hb Hs' Hs//.
  Qed.

  Inductive ssteps  : IT → stateO → IT → stateO → nat → Prop :=
  | ssteps_zero α β σ σ' : α ≡ β → σ ≡ σ' → ssteps α σ β σ' 0
  | ssteps_many α1 σ1 α2 σ2 α3 σ3 n2 :
    sstep α1 σ1 α2 σ2 →
    ssteps α2 σ2 α3 σ3 n2 →
    ssteps α1 σ1 α3 σ3 (1+n2).
  #[export] Instance ssteps_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (=) ==> (iff)) ssteps.
  Proof.
    intros α α' Ha σ σ' Hs β β' Hb σ2 σ2' Hs2 n1 n2 Hnm.
    fold_leibniz. simplify_eq/=.
    split.
    - intro HS. revert α' β' σ' σ2' Ha Hb Hs Hs2.
      induction HS=>α' β' σ'' σ2' Ha Hb Hs Hs2.
      + constructor.
        ++ rewrite -Ha -Hb//.
        ++ rewrite -Hs -Hs2//.
      + econstructor; last first.
        ++ eapply IHHS; eauto.
        ++ rewrite -Ha -Hs//.
    - intro HS. revert α β σ σ2 Ha Hb Hs Hs2.
      induction HS=>α' β' σ'' σ2' Ha Hb Hs Hs2.
      + constructor.
        ++ rewrite Ha Hb//.
        ++ rewrite Hs Hs2//.
      + econstructor; last first.
        ++ eapply IHHS; eauto.
        ++ rewrite Ha Hs//.
  Qed.

  Lemma ssteps_tick_n n α σ : ssteps (Tick_n n α) σ α σ n.
  Proof.
    induction n; first by constructor.
    change (S n) with (1+n).
    change (Tick_n (1+n) α) with (Tick $ Tick_n n α).
    econstructor; last eassumption.
    econstructor; reflexivity.
  Qed.
End sstep.

Section istep.
  Context (r : sReifier).
  Notation F := (sReifier_ops r).
  Notation stateF := (sReifier_state r).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Notation stateO := (stateF ♯ IT).

  Context `{!invGS_gen hlc Σ}.
  Notation iProp := (iProp Σ).

  Program Definition istep :
    IT -n> stateO -n> IT -n> stateO -n> iProp :=
    λne α σ β σ', ((α ≡ Tick β ∧ σ ≡ σ')
                   ∨ (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β)))%I.
  Solve All Obligations with solve_proper.

  Program Definition isteps_pre
          (self : IT -n> stateO -n> IT -n> stateO -n> natO -n> iProp):
    IT -n> stateO -n> IT -n> stateO -n> natO -n> iProp :=
    λne α σ β σ' n, ((n ≡ 0 ∧ α ≡ β ∧ σ ≡ σ')
                 ∨ (∃ n' α0 σ0, n ≡ (1+n') ∧ istep α σ α0 σ0 ∧
                     ▷ self α0 σ0 β σ' n'))%I.
  Solve All Obligations with solve_proper.

  Global Instance isteps_pre_ne : NonExpansive isteps_pre.
  Proof. solve_proper. Qed.
  Global Instance isteps_pre_contractive : Contractive isteps_pre.
  Proof. solve_contractive. Qed.
  Definition isteps : IT -n> stateO -n> IT -n> stateO -n> natO -n> iProp
    := fixpoint isteps_pre.

  Lemma isteps_unfold α β σ σ' n :
    isteps α σ β σ' n ≡
      ((n ≡ 0 ∧ α ≡ β ∧ σ ≡ σ')
                 ∨ (∃ n' α0 σ0, n ≡ (1+n') ∧ istep α σ α0 σ0 ∧
                     ▷ isteps α0 σ0 β σ' n'))%I.
  Proof. unfold isteps. apply (fixpoint_unfold isteps_pre _ _ _ _ _) . Qed.


  (** Properties *)
  Lemma isteps_0 α β σ σ' :
    isteps α σ β σ' 0 ≡ (α ≡ β ∧ σ ≡ σ')%I.
  Proof.
    rewrite isteps_unfold. iSplit.
    - iDestruct 1 as "[(_ & $ & $)|H]".
      iExFalso.
      iDestruct "H" as (n' ? ?) "[% HH]".
      fold_leibniz. lia.
    - iDestruct 1 as "[H1 H2]". iLeft; eauto.
  Qed.
  Lemma isteps_S α β σ σ' k :
    isteps α σ β σ' (S k) ≡ (∃ α1 σ1, istep α σ α1 σ1 ∧ ▷ isteps α1 σ1 β σ' k)%I.
  Proof.
    rewrite isteps_unfold. iSplit.
    - iDestruct 1 as "[(% & _ & _)|H]"; first by fold_leibniz; lia.
      iDestruct "H" as (n' ? ?) "[% HH]".
      fold_leibniz. assert (k = n') as -> by lia.
      iExists _,_. eauto with iFrame.
    - iDestruct 1 as (α1 σ1) "[H1 H2]".
      iRight. iExists k,α1,σ1. eauto with iFrame.
  Qed.
  #[export] Instance isteps_persistent α σ β σ' k : Persistent (isteps α σ β σ' k).
  Proof.
    revert α σ. induction k as [|k]=> α σ.
    - rewrite isteps_0. apply _.
    - rewrite isteps_S. apply _.
  Qed.

  Lemma sstep_istep α β σ σ' :
    sstep r α σ β σ' → (⊢ istep α σ β σ').
  Proof.
    inversion 1; simplify_eq/=.
    - iLeft. eauto.
    - iRight. iExists _,_,_. iSplit; eauto.
      iPureIntro.
      trans (reify r (Vis op i k) σ); first solve_proper; eauto.
  Qed.
  Lemma ssteps_isteps α β σ σ' n :
    ssteps r α σ β σ' n → (⊢ isteps α σ β σ' n).
  Proof.
    revert α σ. induction n=> α σ; inversion 1; simplify_eq /=.
    - rewrite isteps_unfold. iLeft. eauto.
    - rewrite isteps_unfold. iRight. iExists n, α2,σ2.
      repeat iSplit; eauto.
      + iApply sstep_istep; eauto.
      + iNext. iApply IHn; eauto.
  Qed.

  Local Lemma tick_safe_externalize α σ :
    (⊢ ∃ β σ', α ≡ Tick β ∧ σ ≡ σ' : iProp) → ∃ β σ', sstep r α σ β σ'.
  Proof.
    intros Hprf.
    destruct (IT_dont_confuse α)
        as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_err_ne). by iApply internal_eq_sym.
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_nat_tick_ne with "Ha").
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_fun_tick_ne with "Ha").
    + exists α',σ. by econstructor; eauto.
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_vis_ne). by iApply internal_eq_sym.
  Qed.

  Local Lemma effect_safe_externalize α σ :
    (⊢ ∃ β σ', (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β)) : iProp) →
    ∃ β σ', sstep r α σ β σ'.
  Proof.
    intros Hprf.
    destruct (IT_dont_confuse α)
        as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' op i k) "[Ha _]". rewrite Ha.
      iApply (IT_vis_err_ne). by iApply internal_eq_sym.
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' op i k) "[Ha _]". rewrite Ha.
      iApply (IT_nat_vis_ne with "Ha").
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' op i k) "[Ha _]". rewrite Ha.
      iApply (IT_fun_vis_ne with "Ha").
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' op i k) "[Ha _]". rewrite Ha.
      iApply (IT_tick_vis_ne with "Ha").
    + destruct (reify r (Vis op i k) σ) as [σ1 α1] eqn:Hr.
      assert ((∃ α' : IT, α1 ≡ Tick α') ∨ (α1 ≡ Err RuntimeErr)) as [[α' Ha']| Ha'].
      { eapply (reify_is_always_a_tick r op i k σ).
        by rewrite Hr. }
      * exists α',σ1. eapply sstep_reify; eauto.
        rewrite Hr -Ha'//.
      * exfalso. eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (β σ' op' i' k') "[_ Hb]".
        assert (reify r (Vis op i k) σ ≡ reify r α σ) as Har.
        { f_equiv. by rewrite Ha. }
        iEval (rewrite -Har) in "Hb".
        iEval (rewrite Hr) in "Hb".
        iPoseProof (prod_equivI with "Hb") as "[_ Hb']".
        simpl. rewrite Ha'.
        iApply (IT_tick_err_ne). iApply (internal_eq_sym with "Hb'").
  Qed.

  Local Lemma istep_safe_disj α σ :
    (∃ β σ', istep α σ β σ')
      ⊢ (∃ β σ', α ≡ Tick β ∧ σ ≡ σ')
      ∨ (∃ β σ', (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β))).
  Proof.
    rewrite -bi.or_exist.
    apply bi.exist_mono=>β.
    rewrite -bi.or_exist//.
  Qed.

  (* this is true only for iProp/uPred? *)
  Definition disjunction_property (P Q : iProp) := (⊢ P ∨ Q) → (⊢ P) ∨ (⊢ Q).

  Lemma istep_safe_sstep α σ :
    (∀ P Q, disjunction_property P Q) →
    (⊢ ∃ β σ', istep α σ β σ') → ∃ β σ', sstep r α σ β σ'.
  Proof.
    intros Hdisj.
    rewrite istep_safe_disj.
    intros [H|H]%Hdisj.
    - by apply tick_safe_externalize.
    - by apply effect_safe_externalize.
  Qed.

  Lemma istep_ITV α αv β σ σ' :
    (IT_to_V α ≡ Some αv ⊢ istep α σ β σ' -∗ False : iProp)%I.
  Proof.
    rewrite /istep/=. iIntros "Hv [[H _]|H]".
    - iRewrite "H" in "Hv". rewrite IT_to_V_Tau.
      iApply (option_equivI with "Hv").
    - iDestruct "H" as (op i k) "[H _]".
      iRewrite "H" in "Hv". rewrite IT_to_V_Vis.
      iApply (option_equivI with "Hv").
  Qed.

  Lemma istep_err σ e β σ' : istep (Err e) σ β σ' ⊢ False.
  Proof.
    rewrite /istep/=. iDestruct 1 as "[[H _]|H]".
    - iApply (IT_tick_err_ne).
      by iApply (internal_eq_sym with "H").
    - iDestruct "H" as (op i k) "[H _]". iApply (IT_vis_err_ne).
      by iApply internal_eq_sym.
  Qed.
  Lemma istep_tick α β σ σ' : istep (Tick α) σ β σ' ⊢ ▷ (β ≡ α) ∧ σ ≡ σ'.
  Proof.
    simpl. iDestruct 1 as "[[H1 H2]|H]".
    - iFrame. iNext. by iApply internal_eq_sym.
    - iDestruct "H" as (op i k) "[H1 H2]".
      iExFalso. iApply (IT_tick_vis_ne with "H1").
  Qed.
  Lemma istep_vis op i ko β σ σ' :
    istep (Vis op i ko) σ β σ' ⊢ reify r (Vis op i ko) σ ≡ (σ', Tick β).
  Proof.
    simpl. iDestruct 1 as "[[H1 H2]|H]".
    - iExFalso. iApply IT_tick_vis_ne.
      by iApply internal_eq_sym.
    - iDestruct "H" as (op' i' ko') "[H1 $]".
  Qed.

  Lemma isteps_val βv β k σ σ' :
    isteps (IT_of_V βv) σ β σ' k ⊢ IT_of_V βv ≡ β ∧ σ ≡ σ' ∧ ⌜k = 0⌝.
  Proof.
    destruct k as[|k].
    - rewrite isteps_0. iDestruct 1 as "[$ $]".
      eauto.
    - rewrite isteps_S. iDestruct 1 as (α1 σ1) "[Hs Hss]".
      iExFalso. iClear "Hss".
      unfold istep. simpl. iDestruct "Hs" as "[[Ht Hs]|Hs]".
      + destruct βv as[n|f]; iSimpl in "Ht".
        ++  iApply (IT_nat_tick_ne with "Ht").
        ++  iApply (IT_fun_tick_ne with "Ht").
      + iDestruct "Hs" as (op i ko) "[Ht Hs]".
        destruct βv as[n|f]; iSimpl in "Ht".
        ++  iApply (IT_nat_vis_ne with "Ht").
        ++  iApply (IT_fun_vis_ne with "Ht").
  Qed.
  Lemma isteps_tick α βv σ σ' k :
    isteps (Tick α) σ (IT_of_V βv) σ' k ⊢ ∃ k' : nat, ⌜k = (1 + k')%nat⌝ ∧ ▷ isteps α σ (IT_of_V βv) σ' k'.
  Proof.
    rewrite isteps_unfold.
    iDestruct 1 as "[[Hk [Ht Hs]] | H]".
    - iExFalso. destruct βv; iSimpl in "Ht".
      ++ iApply (IT_nat_tick_ne).
         by iApply (internal_eq_sym).
      ++ iApply (IT_fun_tick_ne).
         by iApply (internal_eq_sym).
    - iDestruct "H" as (k' α1 σ1) "[% [Hs Hss]]".
      iExists k'. iSplit; first by eauto.
      rewrite istep_tick.
      iDestruct "Hs" as "[Ha Hs]". iNext.
      iRewrite -"Ha". iRewrite "Hs". done.
  Qed.

  Lemma istep_hom (f : IT → IT) `{!IT_hom f} α σ β σ' :
    istep α σ β σ' ⊢ istep (f α) σ (f β) σ' : iProp.
  Proof.
    iDestruct 1 as "[[Ha Hs]|H]".
    - iRewrite "Ha". iLeft. iSplit; eauto. iPureIntro. apply hom_tick.
    - iDestruct "H" as (op i k) "[#Ha Hr]".
      pose (f' := OfeMor f).
      iRight. iExists op,i,(laterO_map f' ◎ k).
      iAssert (f (Vis op i k) ≡ Vis op i (laterO_map f' ◎ k))%I as "Hf".
      { iPureIntro. apply hom_vis. }
      iRewrite "Ha". iRewrite "Ha" in "Hr". iRewrite "Hf".
      iSplit; first done.
      iApply (reify_vis_cont with "Hr").
  Qed.

  Lemma istep_hom_inv α σ β σ' `{!IT_hom f} :
    istep (f α) σ β σ' ⊢@{iProp} ⌜is_Some (IT_to_V α)⌝
    ∨ (IT_to_V α ≡ None ∧ ∃ α', istep α σ α' σ' ∧ ▷ (β ≡ f α')).
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[la Ha]|[op [i [k Ha]]]] ]]].
    - iExFalso. iApply (istep_err σ e β σ').
      iAssert (f α ≡ Err e)%I as "Hf".
      { iPureIntro. by rewrite Ha hom_err. }
      iRewrite "Hf" in "H". done.
    - iLeft. iPureIntro. rewrite Ha IT_to_V_Nat. done.
    - iLeft. iPureIntro. rewrite Ha IT_to_V_Fun. done.
    - iAssert (α ≡ Tick la)%I as "Ha"; first by eauto.
      iAssert (f (Tick la) ≡ Tick (f la))%I as "Hf".
      { iPureIntro. rewrite hom_tick. done. }
      iRight. iRewrite "Ha". iRewrite "Ha" in "H".
      iRewrite "Hf" in "H". rewrite istep_tick.
      iDestruct "H" as "[Hb Hs]". iSplit.
      { by rewrite IT_to_V_Tau. }
      iExists la. iSplit; last eauto.
      unfold istep. iLeft. iSplit; eauto.
    - iRight.
      pose (fi:=OfeMor f).
      iAssert (f α ≡ Vis op i (laterO_map fi ◎ k))%I as "Hf".
      { iPureIntro. by rewrite Ha hom_vis. }
      iRewrite "Hf" in "H".
      rewrite {1}/istep. iSimpl in "H".
      iDestruct "H" as "[[H _]|H]".
      + iExFalso. iApply (IT_tick_vis_ne).
        iApply internal_eq_sym. done.
      + iDestruct "H" as (op' i' k') "[#Ha Hr]".
        iPoseProof (Vis_inj_op' with "Ha") as "<-".
        iPoseProof (Vis_inj' with "Ha") as "[Hi Hk]".
        iPoseProof (reify_input_cont_inv r op i k fi with "Hr") as (α') "[Hr Ha']".
        iAssert (reify r α σ ≡ (σ', Tick α'))%I with "[Hr]" as "Hr".
        { iRewrite -"Hr". iPureIntro. repeat f_equiv.
          apply Ha. }
        iSplit. { iPureIntro. by rewrite Ha IT_to_V_Vis. }
        iExists α'. iFrame "Ha'".
        rewrite /istep. iRight.
        iExists op,i,k. iFrame "Hr".
        iPureIntro. apply Ha.
  Qed.


End istep.

