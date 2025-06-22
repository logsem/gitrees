From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import list vector.
From iris.bi.lib Require Import fixpoint.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify.

Section external_step.
  Context {A} `{!Cofe A} {a : is_ctx_dep}.
  Context (r : sReifier a).
  Notation F := (sReifier_ops r).
  Notation stateF := (sReifier_state r).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateO := (stateF ♯ IT).

  (** ** Reductions at the Prop level *)
  Inductive external_step : IT → stateO → IT → stateO -> listO IT → Prop :=
  | external_step_tick α β σ σ' :
    α ≡ Tick β →
    σ ≡ σ' →
    external_step α σ β σ' []
  | external_step_reify α op i k β σ1 σ2 th :
    α ≡ Vis op i k →
    reify r α σ1 ≡ (σ2, Tick β, th) →
    external_step α σ1 β σ2 th.

  #[export] Instance external_step_proper
    : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (iff)) external_step.
  Proof.
    intros α1 α2 Ha σ1 σ2 Hs β1 β2 Hb σ'1 σ'2 Hs' pool1 pool2 Hp.
    simplify_eq/=. split.
    - induction 1.
      + inversion Hp; subst.
        eapply external_step_tick.
        ++ rewrite -Ha -Hb//.
        ++ rewrite -Hs' -Hs//.
      + eapply external_step_reify.
        ++ rewrite -Ha//.
        ++ rewrite -Hb -Hs' -Hs -Hp //.
           rewrite -H0. repeat f_equiv; eauto.
    - induction 1.
      + inversion Hp; subst.
        eapply external_step_tick.
        ++ rewrite Ha Hb//.
        ++ rewrite Hs' Hs//.
      + eapply external_step_reify.
        ++ rewrite Ha//.
        ++ rewrite Hb Hs' Hs Hp //.
           rewrite -H0. repeat f_equiv; eauto.
  Qed.

  Inductive external_steps : IT → stateO → IT → stateO -> listO IT → nat → Prop :=
  | steps_zero α β σ σ' l : α ≡ β → σ ≡ σ' → l ≡ [] → external_steps α σ β σ' l 0
  | steps_many α1 σ1 α2 σ2 α3 σ3 l1 l2 l3 n2 :
    l3 ≡ l1 ++ l2 →
    external_step α1 σ1 α2 σ2 l1 →
    external_steps α2 σ2 α3 σ3 l2 n2 →
    external_steps α1 σ1 α3 σ3 l3 (S n2).

  #[export] Instance external_steps_proper
    : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (=) ==> (iff)) external_steps.
  Proof.
    intros α α' Ha σ σ' Hs β β' Hb σ2 σ2' Hs2 l1 l2 Hl n1 n2 Hnm.
    fold_leibniz. simplify_eq /=.
    split.
    - intro HS. revert α' β' σ' σ2' Ha Hb Hs Hs2 l2 Hl.
      induction HS=>α' β' σ'' σ2' Ha Hb Hs Hs2 l2' Hl.
      + constructor.
        ++ rewrite -Ha -Hb //.
        ++ rewrite -Hs -Hs2 //.
        ++ rewrite -Hl H1 //.
      + econstructor; last first.
        ++ eapply IHHS; eauto.
        ++ rewrite -Ha -Hs //.
        ++ rewrite -Hl H //.
    - intro HS. revert α β σ σ2 Ha Hb Hs Hs2 l1 Hl.
      induction HS=>α' β' σ'' σ2' Ha Hb Hs Hs2 l1' Hl.
      + constructor.
        ++ rewrite Ha Hb //.
        ++ rewrite Hs Hs2 //.
        ++ rewrite Hl -H1 //.
      + econstructor; last first.
        ++ eapply IHHS; eauto.
        ++ rewrite Ha Hs //.
        ++ rewrite Hl -H //.
  Qed.

  Inductive tp_external_step : listO IT → stateO → listO IT → stateO → Prop :=
  | tp_external_step_atomic ρ1 ρ2 s1 s2 e1 e2 t1 t2 en :
    ρ1 ≡ (t1 ++ e1 :: t2) →
    ρ2 ≡ (t1 ++ e2 :: t2 ++ en) →
    external_step e1 s1 e2 s2 en  →
    tp_external_step ρ1 s1 ρ2 s2.

  #[export] Instance tp_external_step_proper
    : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (iff)) tp_external_step.
  Proof.
    intros α1 α2 Ha σ1 σ2 Hs β1 β2 Hb σ'1 σ'2 Hs'.
    simplify_eq/=. split.
    - induction 1.
      + eapply tp_external_step_atomic.
        ++ rewrite -Ha //.
        ++ rewrite -Hb //.
        ++ rewrite -Hs -Hs' //.
    - induction 1.
      + eapply tp_external_step_atomic.
        ++ rewrite Ha //.
        ++ rewrite Hb //.
        ++ rewrite Hs Hs' //.
  Qed.

  Lemma tp_external_step_mono αs σ βs σ'
    : tp_external_step αs σ βs σ' → length αs <= length βs.
  Proof.
    induction 1 as [????????? H1 H2].
    rewrite H1 H2.
    rewrite !length_app !length_cons length_app.
    apply Nat.add_le_mono_l.
    rewrite -plus_Sn_m.
    apply Nat.le_add_r.
  Qed.

  Lemma external_step_tp_external_step α β σ σ' e1 e2 l
    : external_step α σ β σ' l
      → tp_external_step (e1 ++ α :: e2) σ (e1 ++ β :: e2 ++ l) σ'.
  Proof.
    induction 1 as [???? H1 H2| ???????? H1 H2].
    - econstructor 1; first reflexivity; first last.
      + rewrite H1.
        by constructor.
      + by rewrite app_nil_r.
    - econstructor 1; first reflexivity; first last.
      + rewrite H1.
        econstructor 2; first done.
        setoid_replace (reify r (Vis op i k) σ1) with (reify r α σ1); first done.
        do 2 f_equiv; by symmetry.
      + reflexivity.
  Qed.

  Inductive tp_external_steps : listO IT → stateO → listO IT → stateO → nat → Prop :=
  | tp_steps_zero α β σ σ' : α ≡ β → σ ≡ σ' → tp_external_steps α σ β σ' 0
  | tp_steps_many α1 σ1 α2 σ2 α3 σ3 n2 :
    tp_external_step α1 σ1 α2 σ2 →
    tp_external_steps α2 σ2 α3 σ3 n2 →
    tp_external_steps α1 σ1 α3 σ3 (S n2).

  #[export] Instance tp_external_steps_proper
    : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (=) ==> (iff)) tp_external_steps.
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

  Lemma tp_external_steps_mono αs σ βs σ' k
    : tp_external_steps αs σ βs σ' k → length αs <= length βs.
  Proof.
    induction 1 as [???? H1 H2 | ??????? H1 H2 H3].
    - by rewrite H1.
    - etransitivity; last apply H3.
      eapply tp_external_step_mono; done.
  Qed.

  Lemma external_steps_tp_external_steps α β σ σ' e1 e2 l n
    : external_steps α σ β σ' l n
      → tp_external_steps (e1 ++ α :: e2) σ (e1 ++ β :: e2 ++ l) σ' n.
  Proof.
    intros H.
    revert e2.
    induction H as [ ????? H1 H2 H3 | ?????????? H1 H2 H3 IH]; intros e2.
    - rewrite H1 H2 H3 app_nil_r.
      by constructor.
    - econstructor.
      + by apply external_step_tp_external_step.
      + rewrite H1.
        specialize (IH (e2 ++ l1)).
        rewrite -app_assoc in IH.
        apply IH.
  Qed.

  Lemma external_steps_tick_n n α σ
    : external_steps (Tick_n n α) σ α σ [] n.
  Proof.
    induction n; first by constructor.
    change (S n) with (1+n).
    change (Tick_n (1+n) α) with (Tick $ Tick_n n α).
    econstructor; last eassumption.
    { rewrite app_nil_r; reflexivity. }
    by econstructor.
  Qed.

  Lemma tp_external_steps_tick_n p1 p2 n α σ
    : tp_external_steps (p1 ++ (Tick_n n α) :: p2) σ (p1 ++ α :: p2) σ n.
  Proof.
    induction n; first by constructor.
    change (S n) with (1+n).
    change (Tick_n (1+n) α) with (Tick $ Tick_n n α).
    econstructor; last eassumption.
    apply (tp_external_step_atomic (p1 ++ Tick (Tick_n n α) :: p2)
             (p1 ++ Tick_n n α :: p2)
             σ σ (Tick (Tick_n n α)) (Tick_n n α) p1 p2 []
             (reflexivity _)).
    - by rewrite app_nil_r.
    - by constructor.
  Qed.
End external_step.

Section internal_step.
  Context {A} `{!Cofe A} {a : is_ctx_dep}.
  Context (r : sReifier a).
  Notation F := (sReifier_ops r).
  Notation stateF := (sReifier_state r).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateO := (stateF ♯ IT).

  Context `{!invGS_gen hlc Σ}.
  Notation iProp := (iProp Σ).

  Program Definition internal_step :
    IT -n> stateO -n> IT -n> stateO -n> listO IT -n> iProp :=
    λne α σ β σ' en, ((α ≡ Tick β ∧ σ ≡ σ' ∧ en ≡ [])
                     ∨ (∃ op i k,
                          α ≡ Vis op i k
                          ∧ reify r α σ ≡ (σ', Tick β, en)))%I.
  Solve All Obligations with solve_proper.

  Program Definition internal_steps_pre
    (self : (prodO IT (prodO stateO (prodO IT (prodO stateO (prodO (listO IT) natO))))) -> iProp) :
    (prodO IT (prodO stateO (prodO IT (prodO stateO (prodO (listO IT) natO))))) -> iProp :=
    λ '(α, (σ, (β, (σ'', (l, n))))), ((n ≡ 0 ∧ α ≡ β ∧ σ ≡ σ'' ∧ l ≡ [])
                        ∨ (∃ n' γ σ' l' l'',
                             l ≡ l' ++ l''
                             ∧ n ≡ (S n')
                             ∧ internal_step α σ γ σ' l'
                             ∧ self (γ, (σ', (β, (σ'', (l'', n'))))))
                                     )%I.

  Definition internal_steps'
    : prodO IT (prodO stateO (prodO IT (prodO stateO (prodO (listO IT) natO)))) -> iProp
    := bi_least_fixpoint internal_steps_pre.

  Global Instance internal_steps_pre_ne : ∀ Φ,
    NonExpansive Φ → NonExpansive (internal_steps_pre Φ).
  Proof.
    intros Φ HΦ.
    intros ?.
    intros [x1 [x2 [x3 [x4 [x5 x6]]]]] [y1 [y2 [y3 [y4 [y5 y6]]]]].
    intros [H1 [H2 [H3 [H4 [H5 H6]]]]].
    simpl in *.
    solve_proper.
  Qed.

  Global Instance internal_steps'_ne : NonExpansive internal_steps'.
  Proof.
    apply least_fixpoint_ne'.
    apply _.
  Qed.

  Global Instance internal_steps_mono : BiMonoPred internal_steps_pre.
  Proof.
    constructor; last apply _.
    iIntros (Φ Ψ HΦ HΨ) "H".
    iIntros ([x1 [x2 [x3 [x4 [x5 x6]]]]])
      "[(G1 & G2 & G3 & G4) | (%n' & %γ & %σ & %l & %l' & G1 & G2 & G3 & G4)]".
    - iLeft; repeat iSplit; done.
    - iRight.
      iExists n', γ, σ, l, l'.
      repeat iSplit; [done | done | done |].
      by iApply "H".
  Qed.

  Lemma internal_steps'_unfold x : internal_steps' x ≡ internal_steps_pre internal_steps' x.
  Proof. apply least_fixpoint_unfold. apply _. Qed.

  Program Definition internal_steps
    : IT -n> stateO -n> IT -n> stateO -n> listO IT -n> natO -n> iProp
    := λne x1 x2 x3 x4 x5 x6, internal_steps' (x1, (x2, (x3, (x4, (x5, x6))))).
  Solve All Obligations with solve_proper.

  Lemma internal_steps_unfold α β σ σ'' n l :
    internal_steps α σ β σ'' l n ≡
      ((n ≡ 0 ∧ α ≡ β ∧ σ ≡ σ'' ∧ l ≡ [])
       ∨ (∃ n' γ σ' l' l'',
            l ≡ l' ++ l''
            ∧ n ≡ (S n')
            ∧ internal_step α σ γ σ' l'
            ∧ internal_steps γ σ' β σ'' l'' n'))%I.
  Proof. rewrite /internal_steps /= internal_steps'_unfold //=. Qed.

  Lemma internal_steps_ind α β σ σ' n l
    Φ `{!NonExpansive Φ}
    : □ (∀ y, internal_steps_pre (bi_least_fixpoint (λ Ψ a, Φ a ∧ internal_steps_pre Ψ a)) y -∗ Φ y)
      -∗ internal_steps α σ β σ' l n -∗ Φ (α, (σ, (β, (σ', (l, n))))).
  Proof.
    rewrite /internal_steps.
    iIntros "H".
    iSimpl; iIntros "G".
    iApply (least_fixpoint_ind_wf with "H G").
  Qed.

  Opaque internal_steps.

  (** Properties *)
  Lemma internal_steps_0 α β σ σ' l :
    internal_steps α σ β σ' l 0 ≡ (α ≡ β ∧ σ ≡ σ' ∧ l ≡ [])%I.
  Proof.
    rewrite internal_steps_unfold. iSplit.
    - iDestruct 1 as "[(_ & $ & $)|H]".
      iExFalso.
      iDestruct "H" as (n' ? ? ?) "[% [_ [%HH _]]]".
      fold_leibniz. lia.
    - iDestruct 1 as "[H1 H2]". iLeft; eauto.
  Qed.

  Lemma internal_steps_S α β σ σ'' l k :
    internal_steps α σ β σ'' l (S k) ≡
      (∃ γ σ' l' l'',
         l ≡ l' ++ l''
         ∧ internal_step α σ γ σ' l'
         ∧ internal_steps γ σ' β σ'' l'' k)%I.
  Proof.
    rewrite internal_steps_unfold. iSplit.
    - iDestruct 1 as "[(% & _ & _)|H]"; first by fold_leibniz; lia.
      iDestruct "H" as (n' ? ? ? ?) "(H1 & [% (H2 & H3)])".
      fold_leibniz. assert (k = n') as -> by lia.
      iExists _,_,_. eauto with iFrame.
    - iDestruct 1 as (γ σ' l' l'') "[H1 [H2 H3]]".
      iRight.
      iExists k,γ,σ',l',l''.
      eauto with iFrame.
  Qed.

  Program Definition tp_internal_step :
    listO IT -n> stateO -n> listO IT -n> stateO -n> iProp :=
    λne α σ β σ', (∃ α0 α1 γ γ' en,
                    α ≡ (α0 ++ γ :: α1)
                    ∧ β ≡ (α0 ++ γ' :: α1 ++ en)
                    ∧ internal_step γ σ γ' σ' en)%I.
  Solve All Obligations with solve_proper.

  Global Instance tp_internal_step_ne : NonExpansive tp_internal_step.
  Proof. solve_proper. Qed.

  Program Definition tp_internal_steps_pre
    (self : prodO (listO IT) (prodO stateO (prodO (listO IT) (prodO stateO natO))) -> iProp) :
    prodO (listO IT) (prodO stateO (prodO (listO IT) (prodO stateO natO))) -> iProp :=
    λ '(α, (σ, (β, (σ'', n)))), ((n ≡ 0 ∧ α ≡ β ∧ σ ≡ σ'')
                     ∨ (∃ n' γ σ',
                          n ≡ (S n')
                          ∧ tp_internal_step α σ γ σ'
                          ∧ self (γ, (σ', (β, (σ'', n'))))))%I.

  Definition tp_internal_steps'
    : prodO (listO IT) (prodO stateO (prodO (listO IT) (prodO stateO natO))) -> iProp
    := bi_least_fixpoint tp_internal_steps_pre.

  Global Instance tp_internal_steps_pre_ne : ∀ Φ,
    NonExpansive Φ → NonExpansive (tp_internal_steps_pre Φ).
  Proof.
    intros Φ HΦ.
    intros ?.
    intros [x1 [x2 [x3 [x4 x5]]]] [y1 [y2 [y3 [y4 y5]]]].
    intros [H1 [H2 [H3 [H4 H5]]]].
    simpl in *.
    solve_proper.
  Qed.

  Global Instance tp_internal_steps_pre_proper : ∀ Φ,
    Proper ((≡) ==> (≡)) Φ → Proper ((≡) ==> (≡)) (tp_internal_steps_pre Φ).
  Proof.
    intros Φ HΦ.
    intros [x1 [x2 [x3 [x4 x5]]]] [y1 [y2 [y3 [y4 y5]]]].
    intros [H1 [H2 [H3 [H4 H5]]]].
    simpl in *.
    solve_proper.
  Qed.

  Global Instance tp_internal_steps'_ne : NonExpansive tp_internal_steps'.
  Proof.
    apply least_fixpoint_ne'.
    apply _.
  Qed.

  Global Instance tp_internal_steps'_proper : Proper ((≡) ==> (≡)) tp_internal_steps'.
  Proof.
    apply least_fixpoint_proper.
    solve_proper.
  Qed.

  Global Instance tp_internal_steps_mono : BiMonoPred tp_internal_steps_pre.
  Proof.
    constructor; last apply _.
    iIntros (Φ Ψ HΦ HΨ) "H".
    iIntros ([x1 [x2 [x3 [x4 x5]]]])
      "[(G1 & G2 & G3) | (%n' & %γ & %σ & G1 & G2 & G3)]".
    - iLeft; repeat iSplit; done.
    - iRight.
      iExists n', γ, σ.
      repeat iSplit; [done | done |].
      by iApply "H".
  Qed.

  Lemma tp_internal_steps'_unfold x : tp_internal_steps' x ≡ tp_internal_steps_pre tp_internal_steps' x.
  Proof. apply least_fixpoint_unfold. apply _. Qed.

  Program Definition tp_internal_steps
    : listO IT -n> stateO -n> listO IT -n> stateO -n> natO -n> iProp
    := λne x1 x2 x3 x4 x5, tp_internal_steps' (x1, (x2, (x3, (x4, x5)))).
  Solve All Obligations with solve_proper.

  Lemma tp_internal_steps_unfold α β σ σ'' n :
    tp_internal_steps α σ β σ'' n ≡
      ((n ≡ 0 ∧ α ≡ β ∧ σ ≡ σ'')
       ∨ (∃ n' γ σ',
            n ≡ (S n')
            ∧ tp_internal_step α σ γ σ'
            ∧ tp_internal_steps γ σ' β σ'' n'))%I.
  Proof. rewrite /tp_internal_steps /= tp_internal_steps'_unfold //=. Qed.

  Lemma tp_internal_steps_ind α β σ σ' l
    Φ `{!NonExpansive Φ}
    : □ (∀ y, tp_internal_steps_pre (bi_least_fixpoint (λ Ψ a, Φ a ∧ tp_internal_steps_pre Ψ a)) y -∗ Φ y)
      -∗ tp_internal_steps α σ β σ' l -∗ Φ (α, (σ, (β, (σ', l)))).
  Proof.
    rewrite /tp_internal_steps.
    iIntros "H".
    iSimpl; iIntros "G".
    iApply (least_fixpoint_ind_wf with "H G").
  Qed.

  Opaque tp_internal_steps.

  (** Properties *)
  Lemma tp_internal_steps_0 α β σ σ' :
    tp_internal_steps α σ β σ' 0 ≡ (α ≡ β ∧ σ ≡ σ')%I.
  Proof.
    rewrite tp_internal_steps_unfold. iSplit.
    - iDestruct 1 as "[(_ & $ & $)|H]".
      iExFalso.
      iDestruct "H" as (n' ? ?) "[% HH]".
      fold_leibniz. lia.
    - iDestruct 1 as "[H1 H2]". iLeft; eauto.
  Qed.

  Lemma tp_internal_steps_S α β σ σ'' k :
    tp_internal_steps α σ β σ'' (S k) ≡ (∃ γ σ',
                                tp_internal_step α σ γ σ'
                                ∧ tp_internal_steps γ σ' β σ'' k)%I.
  Proof.
    rewrite tp_internal_steps_unfold. iSplit.
    - iDestruct 1 as "[(% & _ & _)|H]"; first by fold_leibniz; lia.
      iDestruct "H" as (n' ? ?) "[% HH]".
      iDestruct "HH" as "(H1 & H2)".
      fold_leibniz. assert (k = n') as -> by lia.
      iExists _,_. eauto with iFrame.
    - iDestruct 1 as (γ σ') "[H1 H2]".
      iRight.
      iExists k,γ,σ'.
      eauto with iFrame.
  Qed.

  #[export] Instance internal_step_persistent α σ β σ' en
    : Persistent (internal_step α σ β σ' en).
  Proof. apply _. Qed.

  #[export] Instance internal_steps_persistent α σ β σ' en k
    : Persistent (internal_steps α σ β σ' en k).
  Proof.
    revert α σ en. induction k as [|k]=> α σ en.
    - rewrite internal_steps_0. apply _.
    - rewrite internal_steps_S. apply _.
  Qed.

  #[export] Instance tp_internal_step_persistent α σ β σ'
    : Persistent (tp_internal_step α σ β σ').
  Proof. apply _. Qed.

  #[export] Instance tp_internal_steps_persistent α σ β σ' k
    : Persistent (tp_internal_steps α σ β σ' k).
  Proof.
    revert α σ. induction k as [|k]=> α σ.
    - rewrite tp_internal_steps_0. apply _.
    - rewrite tp_internal_steps_S. apply _.
  Qed.

  Lemma tp_internal_step_decomp α β σ σ' :
    ⊢ tp_internal_step α σ β σ' -∗ ∃ β1 β2 : listO IT, β ≡ β1 ++ β2 ∗ length α ≡ length β1.
  Proof.
    iIntros "H".
    iDestruct "H" as "(%a1 & %a2 & %b1 & %b2 & %c3 & H1 & H2 & H3)".
    iExists (a1 ++ b2 :: a2), c3.
    iSplit.
    - rewrite app_comm_cons.
      by rewrite -app_assoc.
    - iRewrite "H1".
      rewrite !length_app //.
  Qed.

  Lemma external_step_internal_step α β σ σ' en :
    external_step r α σ β σ' en → (⊢ internal_step α σ β σ' en).
  Proof.
    inversion 1; simplify_eq/=.
    - iLeft. eauto.
    - iRight. iExists _,_,_. iSplit; eauto.
  Qed.

  Lemma external_steps_internal_steps α β σ σ' en k :
    external_steps r α σ β σ' en k → (⊢ internal_steps α σ β σ' en k).
  Proof.
    induction 1.
    - by iApply internal_steps_0.
    - iApply internal_steps_S.
      iExists _,_,_,_; iSplit; first done.
      iSplit; [by iApply external_step_internal_step | done].
  Qed.

  Lemma tp_external_step_tp_internal_step α β σ σ' :
    tp_external_step r α σ β σ' → (⊢ tp_internal_step α σ β σ').
  Proof.
    inversion 1 as [????????? H1 H2 H3]; simplify_eq.
    iPoseProof (external_step_internal_step e1 e2 σ σ' en H3) as "H".
    iExists _, _, _, _, _.
    iSplit; first eauto.
    iSplit; first eauto.
    done.
  Qed.

  Lemma tp_external_steps_tp_internal_steps α β σ σ' n :
    tp_external_steps r α σ β σ' n → (⊢ tp_internal_steps α σ β σ' n).
  Proof.
    revert α σ. induction n as [| ? IH] => α σ; inversion 1; simplify_eq /=.
    - rewrite tp_internal_steps_unfold. iLeft. eauto.
    - rewrite tp_internal_steps_unfold. iRight. iExists n, _, _.
      iSplit; first eauto.
      iSplit.
      + iApply tp_external_step_tp_internal_step; eauto.
      + iApply IH; eauto.
  Qed.

  Local Lemma tick_safe_externalize (α : IT) σ :
    (⊢ ∃ β σ', α ≡ Tick β ∧ σ ≡ σ' : iProp) → ∃ β σ', external_step r α σ β σ' [].
  Proof.
    intros Hprf.
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_err_ne). iApply internal_eq_sym.
      by iApply "Ha".
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_ret_tick_ne with "Ha").
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_fun_tick_ne with "Ha").
    + exists α',σ. by econstructor; eauto.
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_vis_ne). by iApply (internal_eq_sym with "Ha").
  Qed.

  (* ctx-free steps *)
  Local Lemma effect_safe_externalize (α : IT) σ :
    (⊢ ∃ β σ' en, (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β, en)) : iProp) →
    ∃ β σ' en, external_step r α σ β σ' en.
  Proof.
    intros Hprf.
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_vis_err_ne). iApply internal_eq_sym.
      by iApply "Ha".
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_ret_vis_ne with "Ha").
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_fun_vis_ne with "Ha").
    + exfalso. eapply uPred.pure_soundness.
      iPoseProof (Hprf) as "H".
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_tick_vis_ne with "Ha").
    + destruct (reify r (Vis op i k) σ) as [[σ1 α1] en] eqn:Hr.
      assert ((∃ α' : IT, α1 ≡ Tick α') ∨ (α1 ≡ Err RuntimeErr)) as [[α' Ha']| Ha'].
      { eapply (reify_is_always_a_tick r op i k σ).
        by rewrite Hr.
      }
      * exists α',σ1, en. eapply external_step_reify; eauto.
        rewrite -Ha' -Hr; repeat f_equiv; eauto.
      * exfalso. eapply uPred.pure_soundness.
        iPoseProof (Hprf) as "H".
        iDestruct "H" as (β σ' en' op' i' k') "[_ Hb]".
        assert (reify r (Vis op i k) σ ≡ reify r α σ) as Har.
        { f_equiv. by rewrite Ha. }
        iEval (rewrite -Har) in "Hb".
        iEval (rewrite Hr) in "Hb".
        iPoseProof (prod_equivI with "Hb") as "[Hb'' Hb']".
        iPoseProof (prod_equivI with "Hb''") as "[_ Hb'''']".
        simpl. rewrite Ha'.
        iApply (IT_tick_err_ne). iApply (internal_eq_sym with "Hb''''").
  Qed.

  Local Lemma internal_step_safe_disj α σ :
    (∃ β σ' en, internal_step α σ β σ' en)
    ⊢ (∃ β σ', α ≡ Tick β ∧ σ ≡ σ')
      ∨ (∃ β σ' en, (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β, en))).
  Proof.
    rewrite -bi.or_exist.
    apply bi.exist_mono=>β.
    rewrite -bi.or_exist.
    rewrite /internal_step /=.
    iIntros "(%σ' & %en & [(H1 & H2 & H3) | H])".
    - iExists σ'; iLeft; by iFrame.
    - iExists σ'; iRight; by iExists en.
  Qed.

  Local Lemma internal_step_safe_disj'' α σ β σ' en :
    (internal_step α σ β σ' en)
    ⊢ (α ≡ Tick β ∧ σ ≡ σ')
      ∨ ((∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β, en))).
  Proof.
    rewrite /internal_step /=.
    iIntros "[(H1 & H2 & H3) | (%op & %i & %k & H)]".
    - iLeft; by iFrame.
    - iRight.
      iExists op, i, k.
      done.
  Qed.

  Lemma internal_step_tp_internal_step α β σ σ' e1 e2 l
    : ⊢ internal_step α σ β σ' l
      → tp_internal_step (e1 ++ α :: e2) σ (e1 ++ β :: e2 ++ l) σ'.
  Proof.
    iStartProof.
    iIntros "H".
    iExists e1, e2, α, β, l.
    iSplit; first done.
    iSplit; first done.
    done.
  Qed.

  Lemma internal_steps_tp_internal_steps α β σ σ' e1 e2 l n
    : ⊢ internal_steps α σ β σ' l n
      → tp_internal_steps (e1 ++ α :: e2) σ (e1 ++ β :: e2 ++ l) σ' n.
  Proof.
    iStartProof.
    iIntros "H".
    iInduction n as [| n IH] "G" forall (α e2 σ l).
    - rewrite internal_steps_0.
      iDestruct "H" as "(H1 & H2 & H3)".
      iRewrite "H1"; iRewrite "H2"; iRewrite "H3".
      rewrite tp_internal_steps_0.
      by rewrite app_nil_r.
    - rewrite internal_steps_S.
      iDestruct "H" as "(%γ & %σ'' & %t & %t' & G1 & G2 & G3)".
      iApply tp_internal_steps_S.
      iExists (e1 ++ γ :: e2 ++ t), σ''.
      iSplit.
      + by iApply internal_step_tp_internal_step.
      + iSpecialize ("G" $! γ (e2 ++ t) σ'' t').
        rewrite -app_assoc.
        iRewrite - "G1" in "G".
        by iApply "G".
  Qed.

  (* this is true only for iProp/uPred? *)
  Definition disjunction_property (P Q : iProp) := (⊢ P ∨ Q) → (⊢ P) ∨ (⊢ Q).

  Lemma internal_step_safe_external_step α σ :
    (∀ P Q, disjunction_property P Q) →
    (⊢ ∃ β σ' en, internal_step α σ β σ' en) → ∃ β σ' en, external_step r α σ β σ' en.
  Proof.
    intros Hdisj.
    rewrite internal_step_safe_disj.
    intros [H|H]%Hdisj.
    - pose proof (tick_safe_externalize _ _ H) as [β [σ' G]].
      by exists β, σ', [].
    - pose proof (effect_safe_externalize _ _ H) as [β [σ' [en G]]].
      by exists β, σ', en.
  Qed.

  (* Local Lemma internal_step_safe_disj''' r α σ β σ' en : *)
  (*   (internal_step α σ β σ' en) *)
  (*   ⊢ (∃ β σ', α ≡ Tick β ∧ σ ≡ σ') *)
  (*     ∨ ((∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β, en))). *)
  (* Proof. *)
  (*   rewrite -bi.or_exist. *)
  (*   apply bi.exist_mono=>β. *)
  (*   rewrite -bi.or_exist. *)
  (*   rewrite /internal_step /=. *)
  (*   iIntros "(%σ' & %en & [(H1 & H2 & H3) | H])". *)
  (*   - iExists σ'; iLeft; by iFrame. *)
  (*   - iExists σ'; iRight; by iExists en. *)
  (* Qed. *)

  (* Lemma sdfsddfds α σ β st' k' *)
  (*   (Hdisj : ∀ P Q, disjunction_property P Q) : *)
  (*   (⊢ tp_internal_steps α σ β st' k') *)
  (*   → (tp_external_steps r α σ β st' k'). *)
  (* Proof. *)
  (*   (* revert α β σ st'. *) *)
  (*   (* induction k' as [| IH]; intros α β σ σ'. *) *)
  (*   intros H. *)
  (*   rewrite tp_internal_steps_unfold in H. *)
  (*   apply Hdisj in H. *)
  (*   destruct H. *)
  (*   - pose proof H as H'. *)
  (*     rewrite bi.and_elim_l in H'. *)
  (*     apply uPred.internal_eq_soundness in H'. *)
  (*     rewrite H'. clear H'. *)
  (*     pose proof H as H'. *)
  (*     rewrite bi.and_elim_r in H'. *)
  (*     pose proof H' as H''. *)
  (*     rewrite bi.and_elim_l in H'. *)
  (*     rewrite bi.and_elim_r in H''. *)
  (*     apply uPred.internal_eq_soundness in H'. *)
  (*     apply uPred.internal_eq_soundness in H''. *)
  (*     rewrite H' H''. *)
  (*     by constructor. *)
  (*   - admit. *)

  (* α ≡ α0 ++ γ :: α1 ∧ β ≡ α0 ++ γ' :: α1 ++ en ∧ internal_step γ σ γ' σ' en *)
  (* Local Lemma tp_internal_step_safe_disj α σ : *)
  (*   (∃ β σ', tp_internal_step α σ β σ') *)
  (*   ⊢ (∃ β σ', α ≡ Tick β ∧ σ ≡ σ') *)
  (*     ∨ (∃ β σ' en, (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β, en))). *)
  (* Proof. *)
  (*   rewrite -bi.or_exist. *)
  (*   apply bi.exist_mono=>β. *)
  (*   rewrite -bi.or_exist. *)
  (*   rewrite /internal_step /=. *)
  (*   iIntros "(%σ' & %en & [(H1 & H2 & H3) | H])". *)
  (*   - iExists σ'; iLeft; by iFrame. *)
  (*   - iExists σ'; iRight; by iExists en. *)
  (* Qed. *)

  (* Lemma tp_internal_step_safe_tp_external_step α σ : *)
  (*   (∀ P Q, disjunction_property P Q) → *)
  (*   (⊢ ∃ β σ', tp_internal_step α σ β σ') → ∃ β σ', tp_external_step r α σ β σ'. *)
  (* Proof. *)
  (*   intros Hdisj. *)
  (*   rewrite internal_step_safe_disj. *)
  (*   intros [H|H]%Hdisj. *)
  (*   - pose proof (tick_safe_externalize _ _ H) as [β [σ' G]]. *)
  (*     by exists β, σ', []. *)
  (*   - pose proof (effect_safe_externalize _ _ H) as [β [σ' [en G]]]. *)
  (*     by exists β, σ', en. *)
  (* Qed. *)

  Local Lemma tick_safe_externalize_model (α : IT) σ :
    (∃ β σ', α ≡ Tick β ∧ σ ≡ σ' : iProp) -∗ ⌜∃ β σ', external_step r α σ β σ' []⌝.
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso.
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_err_ne). iApply internal_eq_sym.
      by iApply "Ha".
    + iExFalso.
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_ret_tick_ne with "Ha").
    + iExFalso.
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_fun_tick_ne with "Ha").
    + iExists α', σ. iPureIntro. by econstructor; eauto.
    + iExFalso.
      iDestruct "H" as (β σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_vis_ne). by iApply (internal_eq_sym with "Ha").
  Qed.

  (* ctx-free steps *)
  Local Lemma effect_safe_externalize_model (α : IT) σ :
    (∃ β σ' en, (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick β, en)) : iProp) -∗
    ⌜∃ β σ' en, external_step r α σ β σ' en⌝.
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso.
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_vis_err_ne). iApply internal_eq_sym.
      by iApply "Ha".
    + iExFalso.
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_ret_vis_ne with "Ha").
    + iExFalso.
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_fun_vis_ne with "Ha").
    + iExFalso.
      iDestruct "H" as (β σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_tick_vis_ne with "Ha").
    + destruct (reify r (Vis op i k) σ) as [[σ1 α1] en] eqn:Hr.
      assert ((∃ α' : IT, α1 ≡ Tick α') ∨ (α1 ≡ Err RuntimeErr)) as [[α' Ha']| Ha'].
      { eapply (reify_is_always_a_tick r op i k σ).
        by rewrite Hr.
      }
      * iExists α',σ1, en.
        iPureIntro.
        eapply external_step_reify; eauto.
        rewrite -Ha' -Hr; repeat f_equiv; eauto.
      * iExFalso.
        iDestruct "H" as (β σ' en' op' i' k') "[_ Hb]".
        assert (reify r (Vis op i k) σ ≡ reify r α σ) as Har.
        { f_equiv. by rewrite Ha. }
        iEval (rewrite -Har) in "Hb".
        iEval (rewrite Hr) in "Hb".
        iPoseProof (prod_equivI with "Hb") as "[Hb'' Hb']".
        iPoseProof (prod_equivI with "Hb''") as "[_ Hb'''']".
        simpl. rewrite Ha'.
        iApply (IT_tick_err_ne). iApply (internal_eq_sym with "Hb''''").
  Qed.

  Lemma internal_step_safe_external_step_model α σ :
    (∃ β σ' en, internal_step α σ β σ' en) -∗ ⌜∃ β σ' en, external_step r α σ β σ' en⌝.
  Proof.
    iIntros "H".
    iDestruct (internal_step_safe_disj α σ with "H") as "[G|G]".
    -iPoseProof (tick_safe_externalize_model _ _ with "G") as "(%β & %σ' & %G)".
      iPureIntro.
      by exists β, σ', [].
    - iPoseProof (effect_safe_externalize_model _ _ with "G") as "(%β & %σ' & %en & %G)".
      iPureIntro.
      by exists β, σ', en.
  Qed.

  Local Lemma internal_step_safe_disj' α σ β :
    (∃ σ' en, internal_step α σ (Ret β) σ' en)
    ⊢ (∃ σ', α ≡ Tick (Ret β) ∧ σ ≡ σ')
      ∨ (∃ σ' en, (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick (Ret β), en))).
  Proof.
    rewrite -bi.or_exist.
    rewrite /internal_step /=.
    iIntros "(%σ' & %en & [(H1 & H2 & H3) | H])".
    - iExists σ'; iLeft; by iFrame.
    - iExists σ'; iRight; by iExists en.
  Qed.

  Lemma ret_discrete_pure `{!OfeDiscrete A} α (β : A) :
    (α ≡ Ret (E := F) (A := A) β -∗ ⌜α ≡ Ret β⌝ : iProp).
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso. rewrite Ha.
      iApply IT_ret_err_ne. iApply internal_eq_sym.
      by iApply "H".
    + rewrite Ha.
      iDestruct (Ret_inj' with "H") as "%K".
      iPureIntro.
      by rewrite K.
    + iExFalso. rewrite Ha.
      iApply IT_ret_fun_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExFalso. rewrite Ha.
      iApply IT_ret_tick_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExFalso. rewrite Ha.
      iApply IT_ret_vis_ne. iApply internal_eq_sym.
      by iApply "H".
  Qed.

  Lemma ret_discrete_pure' α (β : A) :
    (α ≡ Ret (E := F) (A := A) β -∗ ⌜∃ β, α ≡ Ret β⌝ : iProp).
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso. rewrite Ha.
      iApply IT_ret_err_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExists n.
      done.
    + iExFalso. rewrite Ha.
      iApply IT_ret_fun_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExFalso. rewrite Ha.
      iApply IT_ret_tick_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExFalso. rewrite Ha.
      iApply IT_ret_vis_ne. iApply internal_eq_sym.
      by iApply "H".
  Qed.

  Lemma fun_discrete_pure' α β :
    (α ≡ Fun (E := F) (A := A) β -∗ ⌜∃ β, α ≡ Fun β⌝ : iProp).
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso. rewrite Ha.
      iApply IT_fun_err_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExFalso. rewrite Ha.
      iApply IT_ret_fun_ne.
      by iApply "H".
    + iExists g.
      done.
    + iExFalso. rewrite Ha.
      iApply IT_fun_tick_ne. iApply internal_eq_sym.
      by iApply "H".
    + iExFalso. rewrite Ha.
      iApply IT_fun_vis_ne. iApply internal_eq_sym.
      by iApply "H".
  Qed.

  Local Lemma tick_safe_externalize_model' `{!OfeDiscrete A} (α : IT) σ β :
    (∃ σ', α ≡ Tick (Ret β) ∧ σ ≡ σ' : iProp) -∗ ▷ ⌜∃ σ', external_step r α σ (Ret β) σ' []⌝.
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso.
      iDestruct "H" as (σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_err_ne). iApply internal_eq_sym.
      by iApply "Ha".
    + iExFalso.
      iDestruct "H" as (σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_ret_tick_ne with "Ha").
    + iExFalso.
      iDestruct "H" as (σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_fun_tick_ne with "Ha").
    + iExists σ.
      iDestruct "H" as (σ') "[Ha Hs]".
      iEval (rewrite Ha) in "Ha".
      iDestruct (Tau_inj' with "Ha") as "J".
      iDestruct (later_equivI_1 with "J") as "K".
      iNext.
      iDestruct (ret_discrete_pure with "K") as "%K".
      rewrite Ha K.
      iPureIntro.
      by constructor.
    + iExFalso.
      iDestruct "H" as (σ') "[Ha Hs]". rewrite Ha.
      iApply (IT_tick_vis_ne). by iApply (internal_eq_sym with "Ha").
  Qed.

  Local Lemma effect_safe_externalize_model' `{!OfeDiscrete A} (α : IT) σ β :
    (∃ σ' en, (∃ op i k, α ≡ Vis op i k ∧ reify r α σ ≡ (σ', Tick (Ret β), en)) : iProp) -∗
    ▷ ⌜∃ σ' en, external_step r α σ (Ret β) σ' en⌝.
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + iExFalso.
      iDestruct "H" as (σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_vis_err_ne). iApply internal_eq_sym.
      by iApply "Ha".
    + iExFalso.
      iDestruct "H" as (σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_ret_vis_ne with "Ha").
    + iExFalso.
      iDestruct "H" as (σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_fun_vis_ne with "Ha").
    + iExFalso.
      iDestruct "H" as (σ' en op i k) "[Ha _]". rewrite Ha.
      iApply (IT_tick_vis_ne with "Ha").
    + iDestruct "H" as (σ' en' op' i' k') "[_ #Hb]".
      assert (reify r (Vis op i k) σ ≡ reify r α σ) as Har.
      { f_equiv. by rewrite Ha. }
      destruct (reify r (Vis op i k) σ) as [[σ1 α1] en] eqn:Hr.
      iAssert ((α1 ≡ Tick (Ret β)))%I as "#H".
      {
        rewrite -Har.
        iPoseProof (prod_equivI with "Hb") as "[Hb'' Hb']".
        iPoseProof (prod_equivI with "Hb''") as "[_ Hb'''']".
        iApply "Hb''''".
      }
      destruct (IT_dont_confuse α1)
        as [[e'' Ha''] | [[n'' Ha''] | [ [g'' Ha''] | [[α''' Ha'']|[op'' [i'' [k'' Ha'']]]] ]]].
      * iExFalso.
        rewrite Ha''.
        iDestruct (internal_eq_sym with "H") as "?".
        iApply IT_tick_err_ne. iAssumption.
      * iExFalso.
        rewrite Ha''.
        iApply IT_ret_tick_ne. iAssumption.
      * iExFalso.
        rewrite Ha''.
        iApply IT_fun_tick_ne. iAssumption.
      * rewrite Ha''.
        iNext.
        iDestruct (ret_discrete_pure with "H") as "%K'".
        iPureIntro.
        exists σ1, en.
        econstructor.
        ++ apply Ha.
        ++ rewrite -Har.
           rewrite Ha''.
           rewrite K'.
           done.
      * iExFalso.
        rewrite Ha''.
        iDestruct (internal_eq_sym with "H") as "?".
        iApply IT_tick_vis_ne. iAssumption.
  Qed.

  Lemma internal_step_safe_external_step_model' `{!OfeDiscrete A} α σ β :
    (∃ σ' en, internal_step α σ (Ret β) σ' en)
    -∗ ▷ ⌜∃ σ' en, external_step r α σ (Ret β) σ' en⌝.
  Proof.
    iIntros "H".
    iDestruct (internal_step_safe_disj' α σ with "H") as "[G|G]".
    - iPoseProof (tick_safe_externalize_model' _ _ with "G") as ">(%σ' & %G)".
      iPureIntro.
      by exists σ', [].
    - iPoseProof (effect_safe_externalize_model' _ _ with "G") as ">(%σ' & %en & %G)".
      iPureIntro.
      by exists σ', en.
  Qed.

  Lemma tp_internal_step_safe_tp_external_step_model `{!OfeDiscrete A} α σ t :
    (∃ β σ', tp_internal_step [α] σ (Ret t :: β) σ')
    -∗ ▷ ⌜∃ β σ', tp_external_step r [α] σ (Ret t :: β) σ'⌝.
  Proof.
    iIntros "(%β & %σ' & #H)".
    iDestruct "H" as "(%α0 & %α1 & %γ & %γ' & %en & #HEQ1 & #HEQ2 & H)".
    iAssert (α0 ≡ nil ∧ α1 ≡ nil)%I as "(HEQ1' & HEQ2')".
    {
      destruct α0 as [| ? α0]; destruct α1 as [| ? α1]; first done; iExFalso.
      - iDestruct (list_equivI with "HEQ1") as "J".
        iSpecialize ("J" $! 1).
        by iDestruct (option_equivI with "J") as "?".
      - iDestruct (list_equivI with "HEQ1") as "J".
        iSpecialize ("J" $! 1).
        destruct α0; simpl; by iDestruct (option_equivI with "J") as "?".
      - iDestruct (list_equivI with "HEQ1") as "J".
        iSpecialize ("J" $! 1).
        destruct α0; simpl; by iDestruct (option_equivI with "J") as "?".
    }
    iRewrite "HEQ1'" in "HEQ1"; iRewrite "HEQ1'" in "HEQ2".
    iRewrite "HEQ2'" in "HEQ1". iRewrite "HEQ2'" in "HEQ2".
    iSimpl in "HEQ1". iSimpl in "HEQ2".
    iClear "HEQ1' HEQ2'".
    iDestruct (list_equivI with "HEQ1") as "J".
    iSpecialize ("J" $! 0). iSimpl in "J".
    iDestruct (option_equivI with "J") as "J'".
    iDestruct (list_equivI with "HEQ2") as "K".
    iSpecialize ("K" $! 0). iSimpl in "K".
    iDestruct (option_equivI with "K") as "K'".
    iClear "HEQ1 J K".
    iRewrite - "J'" in "H".
    iRewrite - "K'" in "H".

    iApply (bi.pure_mono (∃ σ' en, external_step r α σ (Ret t) σ' en)).
    {
      intros [σ'' [en' H]].
      exists en', σ''.
      eapply (tp_external_step_atomic r [α] (Ret t :: en') σ σ'' α (Ret t) [] [] en');
        [done | done |].
      apply H.
    }
    iClear "HEQ2 J' K'".
    iApply internal_step_safe_external_step_model'.
    iExists σ', en.
    done.
  Qed.

  (* Lemma tp_internal_steps_safe_tp_external_steps_model *)
  (*   α σ : *)
  (*   (∃ t β σ' m, tp_internal_steps α σ (IT_of_V t :: β) σ' m) *)
  (*   -∗ ▷ ⌜∃ t β σ' m, tp_external_steps r α σ (IT_of_V t :: β) σ' m⌝. *)
  (* Proof. *)
  (*   iIntros "(%t & %β & %σ' & %m & H)".     *)
  (*   iInduction m as [| n IH] "G" forall (α σ). *)
  (*   - rewrite tp_internal_steps_0. *)
  (*     iDestruct "H" as "(H1 & H2)".       *)
  (*     iExists t, β, σ, 0. *)
  (*     iDestruct (list_equivI with "H1") as "K". *)
  (*     iSpecialize ("K" $! 0). iSimpl in "K". *)
  (*     iDestruct (option_equivI with "K") as "K'". *)
  (*     iDestruct (ret_discrete_pure with "K'") as "%K". *)
  (*     iNext. *)
  (*     iPureIntro. *)
  (*     rewrite K. *)
  (*     by constructor. *)
  (*   - rewrite tp_internal_steps_S. *)
  (*     iDestruct "H" as "(%γ & %σ'' & #H1 & #H2)". *)
  (*     iSpecialize ("G" $! γ σ'' with "H2"). iClear "H2". *)
  (*     iDestruct "G" as (β' σ''') ">%G". *)
  (*     iExists β', σ'''. *)

  (*     iAssert (⌜tp_external_step r α σ γ σ''⌝)%I as "%H2". *)
  (*     { *)

  (*       admit. *)
  (*     } *)
  (*     iNext. *)
  (*     iPureIntro. *)
  (*     econstructor; last apply G. *)
  (*     apply H2. *)
  (* Admitted. *)


  (* Lemma internal_steps_safe_external_steps_model *)
  (*   `{!OfeDiscrete A} *)
  (*   α σ β σ' en m : *)
  (*   (internal_steps α σ (Ret β) σ' en m) *)
  (*   -∗ ⌜∃ en σ', external_steps r α σ (Ret β) σ' en m⌝. *)
  (* Proof. *)
  (*   remember (Ret β) as β'. *)
  (*   iIntros "H". *)
  (*   iInduction m as [| n IH] "G" forall (α σ en). *)
  (*   - rewrite internal_steps_0. *)
  (*     iDestruct "H" as "(H1 & H2 & H3)". *)
  (*     rewrite Heqβ'. *)
  (*     iDestruct (ret_discrete_pure with "H1") as "%K". *)
  (*     iExists [], σ. *)
  (*     iPureIntro. *)
  (*     by constructor. *)
  (*   - rewrite internal_steps_S. *)
  (*     iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)". *)
  (*     iSpecialize ("G" $! γ σ'' l'' with "H3"). *)
  (*     iDestruct "G" as (en' σ''') "%H". *)
  (*     iExists en', σ'''. *)

  (* Lemma tp_internal_steps_safe_tp_external_steps_model *)
  (*   `{!Inhabited stateO} *)
  (*   `{!OfeDiscrete A} α σ t m : *)
  (*   (∃ β σ', tp_internal_steps α σ (Ret t :: β) σ' m) *)
  (*   -∗ ▷ ⌜∃ β σ', tp_external_steps r α σ (Ret t :: β) σ' m⌝. *)
  (* Proof. *)
  (*   iIntros "(%β & %σ' & H)".     *)

  (*   iInduction m as [| n IH] "G" forall (α σ). *)
  (*   - rewrite tp_internal_steps_0. *)
  (*     iDestruct "H" as "(H1 & H2)". *)
  (*     destruct α as [| x α]; *)
  (*       first by *)
  (*         ( *)
  (*           iDestruct (list_equivI with "H1") as "K"; *)
  (*           iSpecialize ("K" $! 0); iSimpl in "K"; *)
  (*           iDestruct (option_equivI with "K") as "?" *)
  (*         ). *)
  (*     iExists α, σ. *)
  (*     iDestruct (list_equivI with "H1") as "K". *)
  (*     iSpecialize ("K" $! 0). iSimpl in "K". *)
  (*     iDestruct (option_equivI with "K") as "K'". *)
  (*     iDestruct (ret_discrete_pure with "K'") as "%K". *)
  (*     iNext. *)
  (*     iPureIntro. *)
  (*     rewrite K. *)
  (*     by constructor. *)
  (*   - rewrite tp_internal_steps_S. *)
  (*     iDestruct "H" as "(%γ & %σ'' & #H1 & #H2)".       *)
  (*     iSpecialize ("G" $! γ σ'' with "H2"). iClear "H2". *)
  (*     iDestruct "G" as (β' σ''') ">%G". *)
  (*     iExists β', σ'''. *)

  (*     iAssert (⌜tp_external_step r α σ γ σ''⌝)%I as "%H2". *)
  (*     { *)

  (*       admit. *)
  (*     } *)
  (*     iNext. *)
  (*     iPureIntro. *)
  (*     econstructor; last apply G. *)
  (*     apply H2. *)
  (* Admitted. *)

  Lemma internal_step_ITV α αv β σ σ' en :
    (IT_to_V α ≡ Some αv ⊢ internal_step α σ β σ' en -∗ False : iProp)%I.
  Proof.
    rewrite /internal_step/=. iIntros "Hv [[H _]|H]".
    - iRewrite "H" in "Hv". rewrite IT_to_V_Tau.
      iApply (option_equivI with "Hv").
    - iDestruct "H" as (op i k) "[H _]".
      iRewrite "H" in "Hv". rewrite IT_to_V_Vis.
      iApply (option_equivI with "Hv").
  Qed.

  Lemma internal_step_err σ e β σ' en : internal_step (Err e) σ β σ' en ⊢ False.
  Proof.
    rewrite /internal_step/=. iDestruct 1 as "[[H _]|H]".
    - iApply (IT_tick_err_ne).
      by iApply (internal_eq_sym with "H").
    - iDestruct "H" as (op i k) "[H _]". iApply (IT_vis_err_ne).
      by iApply internal_eq_sym.
  Qed.

  Lemma internal_step_tick α β σ σ' en :
    internal_step (Tick α) σ β σ' en ⊢ ▷ (β ≡ α) ∧ σ ≡ σ' ∧ en ≡ [].
  Proof.
    simpl. iDestruct 1 as "[[H1 [H2 H3]]|H]".
    - iFrame. iNext. by iApply internal_eq_sym.
    - iDestruct "H" as (op i k) "[H1 H2]".
      iExFalso. iApply (IT_tick_vis_ne with "H1").
  Qed.

  Lemma internal_step_vis op i ko β σ σ' en :
    internal_step (Vis op i ko) σ β σ' en ⊢ reify r (Vis op i ko) σ ≡ (σ', Tick β, en).
  Proof.
    simpl. iDestruct 1 as "[[H1 H2]|H]".
    - iExFalso. iApply IT_tick_vis_ne.
      by iApply internal_eq_sym.
    - iDestruct "H" as (op' i' ko') "[H1 $]".
  Qed.

  Lemma internal_steps_val βv β en k σ σ' :
    internal_steps (IT_of_V βv) σ β σ' en k ⊢ IT_of_V βv ≡ β ∧ σ ≡ σ' ∧ ⌜k = 0⌝ ∧ en ≡ [].
  Proof.
    destruct k as[|k].
    - rewrite internal_steps_0. iDestruct 1 as "[$ [$ $]]".
      eauto.
    - rewrite internal_steps_S. iDestruct 1 as (α1 σ1 l' l'') "[Heq [Hs Hss]]".
      iExFalso. iClear "Hss".
      unfold internal_step. simpl. iDestruct "Hs" as "[[Ht Hs]|Hs]".
      + destruct βv as[n|f]; iSimpl in "Ht".
        ++  iApply (IT_ret_tick_ne with "Ht").
        ++  iApply (IT_fun_tick_ne with "Ht").
      + iDestruct "Hs" as (op i ko) "[Ht Hs]".
        destruct βv as[n|f]; iSimpl in "Ht".
        ++  iApply (IT_ret_vis_ne with "Ht").
        ++  iApply (IT_fun_vis_ne with "Ht").
  Qed.

  Lemma internal_steps_tick α βv σ σ' l k :
    internal_steps (Tick α) σ (IT_of_V βv) σ' l k
    ⊢ ∃ k' : nat, ⌜k = (1 + k')%nat⌝ ∧ ▷ internal_steps α σ (IT_of_V βv) σ' l k'.
  Proof.
    rewrite internal_steps_unfold.
    iDestruct 1 as "[[Hk [Ht Hs]] | H]".
    - iExFalso. destruct βv; iSimpl in "Ht".
      ++ iApply (IT_ret_tick_ne).
         iApply (internal_eq_sym with "Ht").
      ++ iApply (IT_fun_tick_ne).
         by iApply (internal_eq_sym with "Ht").
    - iDestruct "H" as (k' α1 σ1 l' l'') "[Hl [% [Hs Hss]]]".
      iExists k'. iSplit; first by eauto.
      rewrite internal_step_tick.
      iDestruct "Hs" as "[Ha [Hs1 Hs2]]". iNext.
      iRewrite -"Ha". iRewrite "Hs1".
      iRewrite "Hl".
      iRewrite "Hs2".
      done.
  Qed.

  Lemma internal_step_safe α σ β σ' en :
    (⊢ internal_step α σ β σ' en)
    → (external_step r α σ β σ' en).
  Proof.
    intros G.
    assert (⊢ ▷ internal_step α σ β σ' en) as H.
    {
      iStartProof.
      iPoseProof G as "H".
      iNext. done.
    }
    clear G.
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + eapply uPred.pure_soundness.
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iExFalso.
      iApply (internal_step_err σ e β σ' en).
      iDestruct (internal_eq_rewrite α
                   (Err e)
                   (λ a, internal_step a σ β σ' en)%I with "[] H") as "H'".
      { solve_proper. }
      { by iPureIntro. }
      done.
    + eapply uPred.pure_soundness.
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iExFalso.
      iApply (internal_step_ITV α (RetV n) β σ σ' en with "[] H").
      iPureIntro.
      rewrite Ha /=.
      by rewrite IT_to_V_Ret.
    + eapply uPred.pure_soundness.
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iExFalso.
      iApply (internal_step_ITV α (FunV g) β σ σ' en with "[] H").
      iPureIntro.
      rewrite Ha /=.
      by rewrite IT_to_V_Fun.
    + rewrite Ha.
      cut (⊢@{iProp} ▷ (β ≡ α' ∧ σ ≡ σ' ∧ en ≡ []))%I.
      {
        intros G.
        apply uPred.later_soundness in G.
        pose proof G as G'.
        rewrite bi.and_elim_l in G'.
        apply uPred.internal_eq_soundness in G'.
        rewrite G'. clear G'.
        pose proof G as G'.
        rewrite bi.and_elim_r in G'.
        rewrite bi.and_elim_l in G'.
        apply uPred.internal_eq_soundness in G'.
        rewrite G'. clear G'.
        pose proof G as G'.
        rewrite bi.and_elim_r in G'.
        rewrite bi.and_elim_r in G'.
        apply uPred.internal_eq_soundness in G'.
        rewrite G'. clear G'.
        by econstructor.
      }
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iDestruct (internal_eq_rewrite α
                   (Tick α')
                   (λ a, internal_step a σ β σ' en)%I with "[] H") as "H'".
      { solve_proper. }
      { by iPureIntro. }
      iPoseProof (internal_step_tick with "H'") as "(J1 & J2 & J3)".
      iNext.
      iFrame "J1 J2 J3".
    + rewrite Ha.
      destruct (reify r (Vis op i k) σ) as [[σ1 α1] en'] eqn:Hr.
      assert ((∃ α1', α1 ≡ Tick α1') ∨ α1 ≡ Err RuntimeErr) as [[α1' Ha']|Ha'].
      {
        pose proof (reify_is_always_a_tick r op i k σ α1 σ1 en') as G.
        apply G.
        by rewrite Hr.
      }
      * cut (⊢@{iProp} ▷ (reify r α σ ≡ (σ', Tick β, en)))%I.
        {
          intros G.
          apply uPred.later_soundness in G.
          apply uPred.internal_eq_soundness in G.
          econstructor; first done.
          rewrite -G.
          f_equiv.
          f_equiv.
          symmetry.
          apply Ha.
        }
        iPoseProof H as "H".
        iDestruct (internal_eq_rewrite α
                     (Vis op i k)
                     (λ a, internal_step a σ β σ' en%I) with "[] H") as "H'".
        { solve_proper. }
        { by iPureIntro. }
        iDestruct (internal_step_vis with "H'") as "H2".
        iNext.
        iRewrite - "H2".
        iPureIntro.
        do 2 f_equiv.
        apply Ha.
      * eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct (internal_eq_rewrite α
                     (Vis op i k)
                     (λ a, internal_step a σ β σ' en)%I with "[] H") as "H'".
        { solve_proper. }
        { by iPureIntro. }
        iDestruct (internal_step_vis with "H'") as "H2".
        rewrite Hr Ha'.
        iExFalso.
        iDestruct (prod_equivI with "H2") as "(G1 & _)".
        iDestruct (prod_equivI with "G1") as "(_ & G4)".
        simpl.
        iApply IT_tick_err_ne. iApply internal_eq_sym. iAssumption.
  Qed.

  Lemma internal_step_safe_agnostic α σ :
    (⊢ ∃ β σ' en, internal_step α σ β σ' en)
    → (∃ β σ' en, external_step r α σ β σ' en).
  Proof.
    intros G.
    assert (⊢ ▷ ∃ β σ' en, internal_step α σ β σ' en) as H.
    {
      iStartProof.
      iPoseProof G as "H".
      iNext. done.
    }
    clear G.
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
    + eapply uPred.pure_soundness.
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iExFalso.
      iDestruct "H" as (β σ' en) "H".
      iApply (internal_step_err σ e β σ' en).
      iDestruct (internal_eq_rewrite α
                   (Err e)
                   (λ a, internal_step a σ β σ' en)%I with "[] H") as "H'".
      { solve_proper. }
      { by iPureIntro. }
      done.
    + eapply uPred.pure_soundness.
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iExFalso.
      iDestruct "H" as (β σ' en) "H".
      iApply (internal_step_ITV α (RetV n) β σ σ' en with "[] H").
      iPureIntro.
      rewrite Ha /=.
      by rewrite IT_to_V_Ret.
    + eapply uPred.pure_soundness.
      apply uPred.later_soundness in H.
      iPoseProof H as "H".
      iExFalso.
      iDestruct "H" as (β σ' en) "H".
      iApply (internal_step_ITV α (FunV g) β σ σ' en with "[] H").
      iPureIntro.
      rewrite Ha /=.
      by rewrite IT_to_V_Fun.
    + setoid_rewrite Ha.
      apply uPred.later_soundness in H.
      exists α', σ, [].
      cut (⊢@{iProp} ▷ internal_step (Tick α') σ α' σ []).
      {
        intros J.
        apply uPred.later_soundness in J.
        by apply internal_step_safe in J.
      }
      iPoseProof H as "H".
      iDestruct "H" as (β σ' en) "H".
      iDestruct (internal_eq_rewrite α
                   (Tick α')
                   (λ a, internal_step a σ β σ' en)%I with "[] H") as "H'".
      { solve_proper. }
      { by iPureIntro. }
      iPoseProof (internal_step_tick with "H'") as "(J1 & J2 & J3)".
      iNext.
      iRewrite "J1" in "H".
      iRewrite - "J2" in "H".
      iRewrite "J3" in "H".
      iDestruct (internal_eq_rewrite
                   α
                   (Tick α')
                   (λ a, internal_step a σ α' σ [])%I with "[] H") as "H''".
      { solve_proper. }
      { by iPureIntro. }
      done.
    + setoid_rewrite Ha.
      destruct (reify r (Vis op i k) σ) as [[σ1 α1] en'] eqn:Hr.
      assert ((∃ α1', α1 ≡ Tick α1') ∨ α1 ≡ Err RuntimeErr) as [[α1' Ha']|Ha'].
      {
        pose proof (reify_is_always_a_tick r op i k σ α1 σ1 en') as G.
        apply G.
        by rewrite Hr.
      }
      * cut (⊢@{iProp} ▷ (reify r α σ ≡ (σ1, Tick α1', en')))%I.
        {
          intros G.
          apply uPred.later_soundness in G.
          apply uPred.internal_eq_soundness in G.
          exists α1', σ1, en'.
          econstructor; first done.
          rewrite -G.
          f_equiv.
          f_equiv.
          symmetry.
          apply Ha.
        }
        iPoseProof H as "H".
        iNext.
        iDestruct "H" as (β σ' en) "H".
        iDestruct (internal_eq_rewrite α
                     (Vis op i k)
                     (λ a, internal_step a σ β σ' en%I) with "[] H") as "H'".
        { solve_proper. }
        { by iPureIntro. }
        iDestruct (internal_step_vis with "H'") as "H2".
        iRewrite - "H2".
        iPureIntro.
        assert (reify r (Vis op i k) σ ≡ (σ1, α1, en')) as Hr'.
        { by rewrite Hr. }
        rewrite Ha' in Hr'.
        rewrite -Hr'.
        do 2 f_equiv.
        apply Ha.
      * eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (β σ' en) "H".
        iDestruct (internal_eq_rewrite α
                     (Vis op i k)
                     (λ a, internal_step a σ β σ' en)%I with "[] H") as "H'".
        { solve_proper. }
        { by iPureIntro. }
        iDestruct (internal_step_vis with "H'") as "H2".
        rewrite Hr Ha'.
        iExFalso.
        iDestruct (prod_equivI with "H2") as "(G1 & _)".
        iDestruct (prod_equivI with "G1") as "(_ & G4)".
        simpl.
        iApply IT_tick_err_ne. iApply internal_eq_sym. iAssumption.
  Qed.

  Lemma internal_steps_safe α σ β σ' en k :
    (⊢ internal_steps α σ β σ' en k)
    → (external_steps r α σ β σ' en k).
  Proof.
    intros G.
    assert (⊢ ▷ internal_steps α σ β σ' en k) as H.
    {
      iStartProof.
      iPoseProof G as "H".
      iNext. done.
    }
    clear G.
    revert H.
    revert α β σ σ' en.
    induction k as [| m IH]; intros α β σ σ' en H.
    - rewrite internal_steps_0 in H.
      apply uPred.later_soundness in H.

      pose proof H as H'.
      rewrite bi.and_elim_l in H'.
      apply uPred.internal_eq_soundness in H'.
      rewrite H'; clear H'.

      pose proof H as H'.
      rewrite bi.and_elim_r in H'.
      rewrite bi.and_elim_l in H'.
      apply uPred.internal_eq_soundness in H'.
      rewrite H'; clear H'.

      pose proof H as H'.
      rewrite bi.and_elim_r in H'.
      rewrite bi.and_elim_r in H'.
      apply uPred.internal_eq_soundness in H'.
      rewrite H'; clear H'.

      by constructor.
    - rewrite internal_steps_S in H.
      destruct (IT_dont_confuse α)
        as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
      + eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
        iExFalso.
        iApply (internal_step_err σ e γ σ'' l').
        iDestruct (internal_eq_rewrite α
                     (Err e)
                     (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
        { solve_proper. }
        { by iPureIntro. }
        done.
      + eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
        iExFalso.
        iApply (internal_step_ITV α (RetV n) γ σ σ'' l' with "[] H2").
        iPureIntro.
        rewrite Ha /=.
        by rewrite IT_to_V_Ret.
      + eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
        iExFalso.
        iApply (internal_step_ITV α (FunV g) γ σ σ'' l' with "[] H2").
        iPureIntro.
        rewrite Ha /=.
        by rewrite IT_to_V_Fun.
      + rewrite Ha.
        eapply (steps_many r _ _ _ _ _ _ [] en en m); first done.
        * apply external_step_tick; reflexivity.
        * apply IH.
          iStartProof.
          apply uPred.later_soundness in H.
          iPoseProof H as "H".
          iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
          iDestruct (internal_eq_rewrite α
                     (Tick α')
                     (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
          { solve_proper. }
          { by iPureIntro. }
          iClear "H2".
          iRewrite "H1".
          iClear "H1". clear H en.
          iPoseProof (internal_step_tick with "H2'") as "(J1 & J2 & J3)".
          iRewrite "J2". iRewrite "J3".
          rewrite app_nil_l.
          iRewrite "J2" in "H2'".
          iRewrite "J3" in "H2'".
          iClear "J2 J3".
          clear σ l'.
          iNext.
          iRewrite - "J1".
          iApply "H3".
      + rewrite Ha.
        destruct (reify r (Vis op i k) σ) as [[σ1 α1] en'] eqn:Hr.
        assert ((∃ α1', α1 ≡ Tick α1') ∨ α1 ≡ Err RuntimeErr) as [[α1' Ha']|Ha'].
        {
          pose proof (reify_is_always_a_tick r op i k σ α1 σ1 en') as G.
          apply G.
          by rewrite Hr.
        }
        * eapply (steps_many r _ _ _ _ _ _ en' (drop (length en') en) en m).
          {
            eapply uPred.internal_eq_soundness.
            apply uPred.later_soundness in H.
            iPoseProof H as "H".
            iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
            iDestruct (internal_eq_rewrite α
                         (Vis op i k)
                         (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
            { solve_proper. }
            { by iPureIntro. }
            iClear "H2".
            iDestruct (internal_step_vis with "H2'") as "H2".
            iClear "H2'".
            rewrite Hr.
            iDestruct (prod_equivI with "H2") as "(_ & G2)".
            simpl.
            iRewrite "H1".
            iRewrite - "G2".
            rewrite drop_app_length.
            done.
          }
          {
            eapply external_step_reify.
            - done.
            - rewrite Hr. rewrite  Ha'. done.
          }
          apply IH.
          apply uPred.later_soundness in H.
          iPoseProof H as "H".
          iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
          iDestruct (internal_eq_rewrite α
                       (Vis op i k)
                       (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
          { solve_proper. }
          { by iPureIntro. }
          iClear "H2".
          iDestruct (internal_step_vis with "H2'") as "H2".
          iClear "H2'".
          rewrite Hr Ha'.
          iDestruct (prod_equivI with "H2") as "(G1 & G2)".
          iDestruct (prod_equivI with "G1") as "(G3 & G4)".
          simpl.
          iRewrite "G3".
          iRewrite - "G2" in "H1".
          iRewrite "H1".
          iNext.
          iRewrite "G4".
          rewrite drop_app drop_all app_nil_l Nat.sub_diag drop_0.
          done.
        * eapply uPred.pure_soundness.
          apply uPred.later_soundness in H.
          iPoseProof H as "H".
          iDestruct "H" as (γ σ'' l' l'') "(H1 & H2 & H3)".
          iDestruct (internal_eq_rewrite α
                       (Vis op i k)
                       (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
          { solve_proper. }
          { by iPureIntro. }
          iClear "H2".
          iDestruct (internal_step_vis with "H2'") as "H2".
          iClear "H2'".
          rewrite Hr Ha'.
          iExFalso.
          iDestruct (prod_equivI with "H2") as "(G1 & _)".
          iDestruct (prod_equivI with "G1") as "(_ & G4)".
          simpl.
          iApply IT_tick_err_ne. iApply internal_eq_sym. iAssumption.
  Qed.

  Lemma internal_steps_safe_agnostic α σ k :
    (⊢ ∃ β σ' en, internal_steps α σ (IT_of_V β) σ' en k)
    → (∃ β σ' en, external_steps r α σ (IT_of_V β) σ' en k).
  Proof.
    intros G.
    assert (⊢ ▷ ∃ β σ' en, internal_steps α σ (IT_of_V β) σ' en k) as H.
    {
      iStartProof.
      iPoseProof G as "H".
      iNext. done.
    }
    clear G.
    revert H.
    revert α σ.
    induction k as [| m IH]; intros α σ H.
    - apply uPred.later_soundness in H.
      setoid_rewrite internal_steps_0 in H.
      destruct (IT_to_V α) as [β |] eqn:HEQ.
      + exists β, σ, [].
        rewrite IT_of_to_V'; last by rewrite -HEQ.
        by constructor.
      + eapply uPred.pure_soundness.
        iExFalso.
        iPoseProof H as "H".
        iDestruct "H" as (β σ' en) "(H1 & H2 & H3)".
        iAssert (IT_to_V α ≡ IT_to_V (IT_of_V β))%I as "J".
        { by iApply f_equivI. }
        rewrite IT_to_of_V.
        rewrite HEQ.
        by iDestruct (option_equivI with "J") as "?".
    - setoid_rewrite internal_steps_S in H.
      destruct (IT_dont_confuse α)
        as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
      + eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (β σ' en γ σ'' l' l'') "(H1 & H2 & H3)".
        iExFalso.
        iApply (internal_step_err σ e γ σ'' l').
        iDestruct (internal_eq_rewrite α
                     (Err e)
                     (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
        { solve_proper. }
        { by iPureIntro. }
        done.
      + eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (β σ' en γ σ'' l' l'') "(H1 & H2 & H3)".
        iExFalso.
        iApply (internal_step_ITV α (RetV n) γ σ σ'' l' with "[] H2").
        iPureIntro.
        rewrite Ha /=.
        by rewrite IT_to_V_Ret.
      + eapply uPred.pure_soundness.
        apply uPred.later_soundness in H.
        iPoseProof H as "H".
        iDestruct "H" as (β σ' en γ σ'' l' l'') "(H1 & H2 & H3)".
        iExFalso.
        iApply (internal_step_ITV α (FunV g) γ σ σ'' l' with "[] H2").
        iPureIntro.
        rewrite Ha /=.
        by rewrite IT_to_V_Fun.
      + setoid_rewrite Ha.
        assert (∃ (β : ITV) (σ' : stateO) (en : listO IT),
                  external_steps r α' σ (IT_of_V β) σ' en m) as [β [σ' [en J]]].
        {
          apply IH.
          iStartProof.
          apply uPred.later_soundness in H.
          iPoseProof H as "H".
          iDestruct "H" as (β σ' en γ σ'' l' l'') "(H1 & H2 & H3)".
          iDestruct (internal_eq_rewrite α
                       (Tick α')
                       (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
          { solve_proper. }
          { by iPureIntro. }
          iClear "H2".
          iRewrite "H1".
          iClear "H1". clear H en.
          iPoseProof (internal_step_tick with "H2'") as "(J1 & J2 & J3)".
          iRewrite "J2". iRewrite "J3".
          iRewrite "J3" in "H2'".
          iClear "J3". clear l'.
          iRewrite "J2" in "H2'".
          iClear "J2".
          clear σ.
          iNext.
          iRewrite - "J1".
          iExists β, σ', l''.
          iApply "H3".
        }
        {
          exists β, σ', en.
          eapply (steps_many r _ _ _ _ _ _ [] en en m); first done.
          * apply external_step_tick; reflexivity.
          * apply J.
        }
      + setoid_rewrite Ha.
        destruct (reify r (Vis op i k) σ) as [[σ1 α1] en'] eqn:Hr.
        assert ((∃ α1', α1 ≡ Tick α1') ∨ α1 ≡ Err RuntimeErr) as [[α1' Ha']|Ha'].
        {
          pose proof (reify_is_always_a_tick r op i k σ α1 σ1 en') as G.
          apply G.
          by rewrite Hr.
        }
        * cut (∃ (β : ITV) (σ' : stateO) (en : listO IT),
                 external_steps r α1' σ1 (IT_of_V β) σ' en m).
          {
            intros [β [σ' [en J]]].
            exists β, σ', (en' ++ en).
            eapply (steps_many r _ _ _ _ _ _ en' en (en' ++ en)); first done.
            - econstructor.
              + reflexivity.
              + rewrite Hr Ha'.
                reflexivity.
            - assumption.
          }
          {
            apply IH.
            apply uPred.later_soundness in H.
            iPoseProof H as "H".
            iDestruct "H" as (β σ' en γ σ'' l' l'') "(H1 & H2 & H3)".
            iDestruct (internal_eq_rewrite α
                         (Vis op i k)
                         (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
            { solve_proper. }
            { by iPureIntro. }
            iClear "H2".
            iDestruct (internal_step_vis with "H2'") as "H2".
            iClear "H2'".
            rewrite Hr Ha'.
            iDestruct (prod_equivI with "H2") as "(G1 & G2)".
            iDestruct (prod_equivI with "G1") as "(G3 & G4)".
            simpl.
            iRewrite "G3".
            iRewrite - "G2" in "H1".
            iRewrite "H1".
            iNext.
            iRewrite "G4".
            iExists β, σ', l''.
            done.
          }
        * eapply uPred.pure_soundness.
          apply uPred.later_soundness in H.
          iPoseProof H as "H".
          iDestruct "H" as (β σ' en γ σ'' l' l'') "(H1 & H2 & H3)".
          iDestruct (internal_eq_rewrite α
                       (Vis op i k)
                       (λ a, internal_step a σ γ σ'' l'%I) with "[] H2") as "H2'".
          { solve_proper. }
          { by iPureIntro. }
          iClear "H2".
          iDestruct (internal_step_vis with "H2'") as "H2".
          iClear "H2'".
          rewrite Hr Ha'.
          iExFalso.
          iDestruct (prod_equivI with "H2") as "(G1 & _)".
          iDestruct (prod_equivI with "G1") as "(_ & G4)".
          simpl.
          iApply IT_tick_err_ne. iApply internal_eq_sym. iAssumption.
  Qed.

  Lemma list_lookup_total_correct_I {X : ofe} `{!Inhabited X} (l : list X) (i : nat) (x : X) :
    ⊢@{iProp} (l !! i ≡ Some x -∗ l !!! i ≡ x)%I.
  Proof.
    iIntros "H".
    rewrite list_lookup_total_alt.
    iRewrite "H".
    done.
  Qed.

  Polymorphic Class FiniteExistential :=
    can_split_or (P Q: nat → Prop):
      (∀ a b, a < b → P b → P a) →
      (∀ a b, a < b → Q b → Q a) →
      (∀ a, P a ∨ Q a) → (∀ a, P a) ∨ (∀ a, Q a).

  Polymorphic Class Classical : Prop :=
    excluded_middle : ∀ P: Prop, P ∨ ¬ P.

  Lemma classical_can_commute_or (P Q : nat → Prop):
    (∀ P : Prop, P ∨ ¬ P) →
    (∀ a b, a < b → P b → P a) →
    (∀ a b, a < b → Q b → Q a) →
    (∀ a, P a ∨ Q a) → (∀ a, P a) ∨ (∀ a, Q a).
  Proof.
    intros xm HdownP HdownQ Hsome.
    destruct (xm (∃ a, ¬ P a)) as [[a' HP]|HP]; last first.
    - left. intros a'. destruct (xm (P a')); auto.
      exfalso. apply HP.
      by exists a'.
    - assert (Q a') by (destruct (Hsome a'); naive_solver).
      right. intros b.
      destruct (le_lt_dec a' b) as [J | J].
      + destruct (le_lt_eq_dec _ _ J) as [K | K].
        * destruct (Hsome b); auto.
          exfalso.
          apply HP.
          eapply HdownP; eauto.
        * by subst.
      + eapply HdownQ; eauto.
  Qed.

  Global Instance classical_finite_existential `{Classical} : FiniteExistential.
  Proof.
    intros P Q ???. eapply classical_can_commute_or; eauto.
  Qed.

  Lemma can_commute_finite_exists `{FiniteExistential} (X : Type)
    (P : X → nat → Prop) (Q: X → Prop) :
    (∀ x a b, a < b → P x b → P x a)
    → (∀ a, ∃ x, Q x ∧ P x a)
    → pred_finite Q
    → ∃ x, ∀ a, P x a.
  Proof.
    intros Hdown Hsome [Y Hfin].
    assert (∀ a, ∃ x, x ∈ Y ∧ P x a) as Hsome'.
    { intros a'. destruct (Hsome a') as [x [? ?]]. exists x. split; eauto. }
    clear Hfin Hsome. induction Y as [|x Y IH].
    - specialize (Hsome' 0) as [x [? ?]]. exfalso. by eapply not_elem_of_nil.
    - assert ((∀ a, P x a) ∨ (∀ a : nat, ∃ x : X, x ∈ Y ∧ P x a)) as [|]; eauto.
      eapply can_split_or; eauto.
      + intros a' b Hab [y [HA HP]]. exists y; split; eauto.
      + intros a'; destruct (Hsome' a') as [y [HA HP]].
        apply elem_of_cons in HA as [<-|?]; eauto.
  Qed.

  Lemma iProp_disj `{Classical} (P Q : iProp)
    : (⊢ P ∨ Q) → (⊢ P) ∨ ⊢ Q.
  Proof.
    intros J.
    destruct (classical_can_commute_or (λ n, uPred_holds P n ε) (λ n, uPred_holds Q n ε)); eauto.
    - intros b c Hbc K.
      eapply uPred_mono; eauto. lia.
    - intros b c Hbc K.
      eapply uPred_mono; eauto. lia.
    - intros n.
      assert (Hemp : uPred_holds (emp : iProp) n ε).
      { uPred.unseal. rewrite /upred.uPred_pure_def //=. }
      pose proof (uPred_in_entails _ _ J n ε (ucmra_unit_validN _) Hemp) as G.
      revert G.
      uPred.unseal.
      rewrite /= /upred.uPred_or_def /=.
      intros [G | G]; by [left | right].
    - left.
      constructor.
      intros n r' Hr Hval.
      eapply uPred_mono; eauto.
      apply ucmra_unit_leastN.
    - right.
      constructor.
      intros n r' Hr Hval.
      eapply uPred_mono; eauto.
      apply ucmra_unit_leastN.
  Qed.

  Lemma iProp_finite_exists `{Classical}
    X `{!EqDecision X} `{!finite.Finite X} (P : X → iProp)
    : (⊢ ∃ a, P a) → ∃ a, ⊢ (P a).
  Proof.
    intros Hexist.
    destruct (can_commute_finite_exists _
                (λ a' n, uPred_holds (P a') n ε) (λ _, True)) as [x' H']; eauto.
    - intros x b c Hbc J.
      eapply uPred_mono; eauto. lia.
    - intros n.
      assert (Hemp : uPred_holds (emp : iProp) n ε).
      { uPred.unseal. rewrite /upred.uPred_pure_def //=. }
      pose proof (uPred_in_entails _ _ Hexist n ε (ucmra_unit_validN _) Hemp) as G.
      revert G.
      uPred.unseal.
      rewrite /= /upred.uPred_exist_def /=.
      intros [b G].
      exists b.
      split; first done.
      apply G.
    - exists (finite.enum X).
      intros.
      apply finite.elem_of_enum.
    - exists x'.
      constructor.
      intros n x Hx Hval.
      eapply uPred_mono; eauto.
      apply ucmra_unit_leastN.
  Qed.

  Lemma tp_internal_steps_safe_agnostic `{C : Classical} α σ k :
    (⊢ ∃ β βs σ', tp_internal_steps α σ ((IT_of_V β) :: βs) σ' k)
    → (∃ β βs σ', tp_external_steps r α σ ((IT_of_V β) :: βs) σ' k).
  Proof.
    intros G.
    assert (⊢ ▷ ∃ β βs σ', tp_internal_steps α σ ((IT_of_V β) :: βs) σ' k) as H.
    {
      iStartProof.
      iPoseProof G as "H".
      iNext. done.
    }
    clear G.
    revert H.
    revert α σ.
    induction k as [| m IH]; intros α σ H.
    - apply uPred.later_soundness in H.
      setoid_rewrite tp_internal_steps_0 in H.
      destruct α as [| α αs].
      {
        eapply uPred.pure_soundness.
        iExFalso.
        iPoseProof H as "H".
        iDestruct "H" as (β βs σ') "(H1 & H2)".
        iDestruct (list_equivI with "H1") as "J".
        iSpecialize ("J" $! 0).
        by iDestruct (option_equivI with "J") as "?".
      }
      destruct (IT_to_V α) as [β |] eqn:HEQ.
      + exists β, αs, σ.
        rewrite IT_of_to_V'; last by rewrite -HEQ.
        by constructor.
      + eapply uPred.pure_soundness.
        iExFalso.
        iPoseProof H as "H".
        iDestruct "H" as (β βs σ') "(H1 & H2)".
        iAssert (IT_to_V α ≡ IT_to_V (IT_of_V β))%I as "J".
        {
          iDestruct (list_equivI with "H1") as "J".
          iSpecialize ("J" $! 0).
          iSimpl in "J".
          iDestruct (option_equivI with "J") as "?".
          by iApply f_equivI.
        }
        rewrite IT_to_of_V.
        rewrite HEQ.
        by iDestruct (option_equivI with "J") as "?".
    - setoid_rewrite tp_internal_steps_S in H.
      cut (∃ (β : ITV) (βs : list IT) (σ' : stateO),
             ∃ γ σ'', tp_external_step r α σ γ σ''
                      ∧ tp_external_steps r γ σ'' (IT_of_V β :: βs) σ' m).
      {
        intros [β [βs [σ' [γ [σ'' [H1 H2]]]]]].
        exists β, βs, σ'.
        eapply tp_steps_many; eassumption.
      }
      rename H into H'.
      assert (⊢ ▷ ∃ (x : list IT * list IT * IT),
                    α ≡ x.1.1 ++ x.2 :: x.1.2
                    ∧
                      ∃ (σ'' : stateO) (δ' : IT) (en : list IT),
                        internal_step x.2 σ δ' σ'' en
                        ∧ ∃ (β : ITV) (βs : list IT) (σ' : stateO),
                            tp_internal_steps (x.1.1 ++ δ' :: x.1.2 ++ en) σ''
                              (IT_of_V β :: βs) σ' m) as H.
      {
        iStartProof.
        iPoseProof H' as "H".
        iNext.
        iDestruct "H" as (β βs σ' γ σ'') "(H1 & H2)".
        iDestruct "H1" as (α0 α1 δ δ' en) "(G1 & G2 & G3)".
        iExists (α0, α1, δ).
        iFrame "G1".
        iExists σ''.
        iExists δ', en.
        iFrame "G3".
        iExists β, βs, σ'.
        iRewrite "G2" in "H2".
        iFrame "H2".
      }
      clear H'.
      cut (∃ (x : list IT * list IT * IT),
             α ≡ x.1.1 ++ x.2 :: x.1.2
             ∧ ∃ (σ'' : stateO) (δ' : IT) (en : list IT),
                 (⊢ internal_step x.2 σ δ' σ'' en)
                 ∧ ⊢ ∃ (β : ITV) (βs : list IT) (σ' : stateO),
                     (tp_internal_steps (x.1.1 ++ δ' :: x.1.2 ++ en)
                          σ'' (IT_of_V β :: βs) σ' m)).
      {
        intros [x [HEQ1 [σ'' [δ' [en [H1 H2]]]]]].
        destruct x as [[α0 α1] δ].
        edestruct IH as [β' [βs' [σ''' J1]]].
        {
          iNext.
          iApply H2.
        }
        exists β', βs', σ''', (α0 ++ δ' :: α1 ++ en), σ''.
        apply internal_step_safe in H1.
        split; last done.
        econstructor; last apply H1.
        - apply HEQ1.
        - reflexivity.
      }
      cut (∃ (x : list IT * list IT * IT),
             α ≡ x.1.1 ++ x.2 :: x.1.2
             ∧ ∃ (σ'' : stateO) (δ' : IT) (en : list IT),
                 ⊢ (internal_step x.2 σ δ' σ'' en)
                 ∧ ∃ (β : ITV) (βs : list IT) (σ' : stateO),
                     (tp_internal_steps (x.1.1 ++ δ' :: x.1.2 ++ en)
                        σ'' (IT_of_V β :: βs) σ' m)).
      {
        intros [x [HEQ1 [σ'' [δ' [en H1]]]]].
        destruct x as [[α0 α1] δ].
        exists (α0, α1, δ).
        split; first done.
        pose proof H1 as H2.
        rewrite bi.and_elim_l in H2.
        rewrite bi.and_elim_r in H1.
        exists σ'', δ', en.
        by split.
      }
      cut (∃ (x : list IT * list IT * IT),
             α ≡ x.1.1 ++ x.2 :: x.1.2
             ∧ ⊢ ∃ (σ'' : stateO) (δ' : IT) (en : list IT),
                   (internal_step x.2 σ δ' σ'' en)
                   ∧ ∃ (β : ITV) (βs : list IT) (σ' : stateO),
                       (tp_internal_steps (x.1.1 ++ δ' :: x.1.2 ++ en)
                          σ'' (IT_of_V β :: βs) σ' m)).
      {
        intros [x [HEQ1 H1]].
        destruct x as [[α0 α1] δ].
        exists (α0, α1, δ).
        split; first done.
        destruct (IT_dont_confuse δ)
          as [[e Ha] | [[n Ha] | [ [g Ha] | [[α' Ha]|[op [i [k Ha]]]] ]]].
        + eapply uPred.pure_soundness.
          iExFalso.
          iPoseProof H1 as "H".
          iDestruct "H" as (σ'' δ' en) "(H1 & _)".
          iApply (internal_step_err σ e δ' σ'' en).
          iDestruct (internal_eq_rewrite δ
                       (Err e)
                       (λ a, internal_step a σ δ' σ'' en%I) with "[] H1") as "H1'".
          { solve_proper. }
          { by iPureIntro. }
          done.
        + eapply uPred.pure_soundness.
          iExFalso.
          iPoseProof H1 as "H".
          iDestruct "H" as (σ'' δ' en) "(H1 & _)".
          iExFalso.
          iApply (internal_step_ITV δ (RetV n) δ' σ σ'' en with "[] H1").
          iPureIntro.
          rewrite Ha /=.
          by rewrite IT_to_V_Ret.
        + eapply uPred.pure_soundness.
          iExFalso.
          iPoseProof H1 as "H".
          iDestruct "H" as (σ'' δ' en) "(H1 & _)".
          iApply (internal_step_ITV δ (FunV g) δ' σ σ'' en with "[] H1").
          iPureIntro.
          rewrite Ha /=.
          by rewrite IT_to_V_Fun.
        + exists σ, α', [].
          apply uPred.later_soundness.
          iDestruct H1 as (σ'' δ' en) "(H1 & H2)".
          iDestruct (internal_eq_rewrite δ
                       (Tick α')
                       (λ a, internal_step a σ δ' σ'' en%I) with "[] H1") as "H1'".
          { solve_proper. }
          { by iPureIntro. }
          iPoseProof (internal_step_tick with "H1'") as "(J1 & J2 & J3)".
          iNext.
          iClear "H1'".
          iRewrite "J1" in "H1".
          iRewrite - "J2" in "H1".
          iRewrite "J3" in "H1".
          iFrame "H1".
          iRewrite "J1" in "H2".
          iRewrite - "J2" in "H2".
          iRewrite "J3" in "H2".
          iFrame "H2".
        + destruct (reify r (Vis op i k) σ) as [[σ1 α1'] en'] eqn:Hr.
          assert ((∃ α1'', α1' ≡ Tick α1'') ∨ α1' ≡ Err RuntimeErr)
            as [[α1''' Ha']|Ha'].
          {
            pose proof (reify_is_always_a_tick r op i k σ α1' σ1 en') as G.
            apply G.
            by rewrite Hr.
          }
          * exists σ1, α1''', en'.
            apply uPred.later_soundness.
            iPoseProof H1 as "H".
            iDestruct "H" as (σ'' δ' en) "(H1 & H2)".
            iDestruct (internal_eq_rewrite δ
                         (Vis op i k)
                         (λ a, internal_step a σ δ' σ'' en%I) with "[] H1") as "H1'".
            { solve_proper. }
            { by iPureIntro. }
            iDestruct (internal_step_vis with "H1'") as "H1''".
            iDestruct (prod_equivI with "H1''") as "(G1 & G2)".
            iDestruct (prod_equivI with "G1") as "(G3 & G4)".
            rewrite Hr.
            iSimpl in "G1 G2 G3 G4".
            iRewrite - "G2" in "H1".
            iRewrite - "G3" in "H1".
            iEval (rewrite Ha') in "G4".
            iNext.
            iRewrite - "G4" in "H1".
            iFrame "H1".
            iRewrite - "G2" in "H2".
            iRewrite - "G3" in "H2".
            iRewrite - "G4" in "H2".
            iFrame "H2".
          * eapply uPred.pure_soundness.
            iPoseProof H1 as "H".
            iDestruct "H" as (σ'' δ' en) "(H1 & H2)".
            iDestruct (internal_eq_rewrite δ
                         (Vis op i k)
                         (λ a, internal_step a σ δ' σ'' en%I) with "[] H1") as "H1'".
            { solve_proper. }
            { by iPureIntro. }
            iDestruct (internal_step_vis with "H1'") as "H1''".
            rewrite Hr Ha'.
            iExFalso.
            iDestruct (prod_equivI with "H1''") as "(G1 & _)".
            iDestruct (prod_equivI with "G1") as "(_ & G4)".
            simpl.
            iApply IT_tick_err_ne. iApply internal_eq_sym. iAssumption.
      }
      apply uPred.later_soundness in H.
      clear IH.
      cut (∃ i : fin (length α),
             ⊢ ∃ (σ'' : stateO) (δ' : IT) (en : list IT),
                 internal_step (Vector.of_list α !!! i) σ δ' σ'' en
                 ∧ ∃ (β : ITV) (βs : list IT) (σ' : stateO),
                     tp_internal_steps
                       (take i (list_to_vec α) ++ δ' :: drop (S i) (list_to_vec α)
                          ++ en) σ''
                       (IT_of_V β :: βs) σ' m).
      {
        intros [i G].
        exists (take i (list_to_vec α), drop (S i) (list_to_vec α), (Vector.of_list α !!! i)).
        split.
        - rewrite /=; rewrite -vec_to_list_take_drop_lookup.
          by rewrite vec_to_list_to_vec.
        - iApply G.
      }
      assert (⊢ ∃ i : fin (length α),
                ∃ (σ'' : stateO) (δ' : IT) (en : list IT),
                  internal_step (Vector.of_list α !!! i) σ δ' σ'' en
                  ∧ ∃ (β : ITV) (βs : list IT) (σ' : stateO),
                      tp_internal_steps
                        (take i (list_to_vec α) ++ δ' :: drop (S i) (list_to_vec α)
                           ++ en) σ''
                        (IT_of_V β :: βs) σ' m).
      {
        iPoseProof H as "H".
        iDestruct "H" as (x) "(H1 & H2)".
        destruct x as [[x1 x2] x3].
        rewrite vec_to_list_to_vec.
        iAssert (⌜∃ i : fin (length α), (i : nat) = length x1⌝)%I as "%J".
        {
          iAssert (⌜length x1 < length α⌝)%I as "%J".
          {
            iDestruct (f_equivI length with "H1") as "%J".
            iPureIntro.
            rewrite /= length_app length_cons in J.
            symmetry in J.
            lia.
          }
          iExists (nat_to_fin J).
          iPureIntro.
          by rewrite fin_to_nat_to_fin.
        }
        destruct J as [i J].
        iExists i.
        iAssert (x3 ≡ list_to_vec α !!! i)%I as "HEQ1".
        {
          iDestruct (list_equivI with "H1") as "H1'".
          iSpecialize ("H1'" $! i).
          iSimpl in "H1 H1'".
          rewrite list_lookup_middle; last done.
          iApply internal_eq_sym.
          iClear "H1 H2".
          clear.
          iPoseProof (list_lookup_total_correct_I (X := IT) (list_to_vec α) i x3 with "[]") as "J".
          - iRewrite - "H1'".
            iPureIntro.
            by rewrite vec_to_list_to_vec.
          - iRewrite - "J".
            iPureIntro.
            match goal with
            | |- context G [?a ≡ ?b] =>
                assert (a = b) as ->; last done
            end.
            rewrite vec_to_list_to_vec.
            rewrite vlookup_lookup.
            rewrite vec_to_list_to_vec.
            apply list_lookup_lookup_total_lt.
            apply fin_to_nat_lt.
        }
        iDestruct "H2" as (σ'' δ' en) "(J1 & J2)".
        iExists σ'', δ', en.
        iSplit.
        { by iRewrite "HEQ1" in "J1". }
        iDestruct "J2" as (β βs σ') "J2".
        iExists β, βs, σ'.
        iSimpl in "J2".
        iAssert ((take i α ++ δ' :: drop (S i) α ++ en) ≡
                   (x1 ++ δ' :: x2 ++ en))%I as "HEQ2".
        {
          iApply list_equivI.
          iIntros (n).
          destruct (lt_eq_lt_dec n i) as [[K | ->] | K].
          - rewrite lookup_app_l.
            + iDestruct (list_equivI with "H1") as "H1'".
              iSpecialize ("H1'" $! n).
              iSimpl in "H1'".
              rewrite lookup_take; last done.
              iRewrite "H1'".
              rewrite lookup_app_l; last (by rewrite -J).
              rewrite lookup_app_l; first done; last (by rewrite -J).
            + rewrite firstn_length_le; first done.
              apply Nat.lt_le_incl.
              apply fin_to_nat_lt.
          - rewrite J.
            rewrite list_lookup_middle.
            + by rewrite list_lookup_middle.
            + rewrite length_take_le; first done.
              rewrite -J.
              apply Nat.lt_le_incl.
              apply fin_to_nat_lt.
          - rewrite lookup_app_r.
            + iDestruct (list_equivI with "H1") as "H1'".
              iSpecialize ("H1'" $! n).
              iSimpl in "H1'".
              rewrite length_take_le; last (apply Nat.lt_le_incl, fin_to_nat_lt).
              rewrite lookup_app_r; last (rewrite -J; by apply Nat.lt_le_incl).
              rewrite lookup_app_r; last (rewrite -J; by apply Nat.lt_le_incl).
              rewrite -J.
              rewrite lookup_cons_ne_0; last lia.
              rewrite lookup_cons_ne_0; last lia.
              rewrite lookup_cons_ne_0; last lia.
              destruct (decide (n < length α)) as [L | L].
              * rewrite lookup_app_l.
                -- rewrite lookup_drop.
                   rewrite Nat.add_pred_r; last lia.
                   rewrite Nat.add_succ_l.
                   rewrite Nat.add_sub_assoc; last lia.
                   rewrite Nat.add_sub' /=.
                   iAssert (⌜Init.Nat.pred (n - i) < length x2⌝)%I as "%J'".
                   {
                     iDestruct (f_equivI length with "H1") as "%J'".
                     iPureIntro.
                     rewrite /= length_app length_cons -J in J'.
                     lia.
                   }
                   iRewrite "H1'".
                   by rewrite lookup_app_l.
                -- rewrite length_drop.
                   rewrite Nat.sub_succ_r.
                   rewrite -Nat.pred_lt_mono; last lia.
                   lia.
              * rewrite lookup_app_r.
                -- iAssert (⌜length x2 <= Init.Nat.pred (n - i)⌝)%I as "%J'".
                   {
                     iDestruct (f_equivI length with "H1") as "%J'".
                     iPureIntro.
                     rewrite /= length_app length_cons -J in J'.
                     lia.
                   }
                   rewrite lookup_app_r; last done.
                   iAssert (⌜length (drop (S i) α) = length x2⌝)%I as "%J''".
                   {
                     rewrite length_drop.
                     iDestruct (f_equivI length with "H1") as "%J''".
                     iPureIntro.
                     rewrite /= length_app length_cons -J in J''.
                     lia.
                   }
                   by rewrite J''.
                -- rewrite length_drop.
                   rewrite Nat.sub_succ_r.
                   lia.
            + rewrite length_take_le; first lia.
              apply Nat.lt_le_incl.
              apply fin_to_nat_lt.
        }
        by iRewrite "HEQ2".
      }
      eapply iProp_finite_exists.
      + apply _.
      + assumption.
  Qed.

End internal_step.

Section internal_step_ctx_indep.
  Context {A} `{!Cofe A}.
  Context (r : sReifier NotCtxDep).
  Notation F := (sReifier_ops r).
  Notation stateF := (sReifier_state r).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateO := (stateF ♯ IT).

  Context `{!invGS_gen hlc Σ}.
  Notation iProp := (iProp Σ).

  Lemma internal_step_hom (f : IT → IT) `{!IT_hom f} α σ β σ' en :
    internal_step r α σ β σ' en ⊢ internal_step r (f α) σ (f β) σ' en : iProp.
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

  Lemma internal_step_hom_inv α σ β σ' en (f : IT → IT) `{!IT_hom f} :
    internal_step r (f α) σ β σ' en ⊢@{iProp} ⌜is_Some (IT_to_V α)⌝
                          ∨ (IT_to_V α ≡ None ∧ ∃ α', internal_step r α σ α' σ' en
                                                      ∧ ▷ (β ≡ f α')).
  Proof.
    iIntros "H".
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[la Ha]|[op [i [k Ha]]]] ]]].
    - iExFalso. iApply (internal_step_err r σ e β σ').
      iAssert (f α ≡ Err e)%I as "Hf".
      { iPureIntro. by rewrite Ha hom_err. }
      iRewrite "Hf" in "H". done.
    - iLeft. iPureIntro. rewrite Ha IT_to_V_Ret. done.
    - iLeft. iPureIntro. rewrite Ha IT_to_V_Fun. done.
    - iAssert (α ≡ Tick la)%I as "Ha"; first by eauto.
      iAssert (f (Tick la) ≡ Tick (f la))%I as "Hf".
      { iPureIntro. rewrite hom_tick. done. }
      iRight. iRewrite "Ha". iRewrite "Ha" in "H".
      iRewrite "Hf" in "H". rewrite internal_step_tick.
      iDestruct "H" as "[Hb Hs]". iSplit.
      { by rewrite IT_to_V_Tau. }
      iExists la. iSplit; last eauto.
      unfold internal_step. iLeft. iSplit; eauto.
    - iRight.
      pose (fi:=OfeMor f).
      iAssert (f α ≡ Vis op i (laterO_map fi ◎ k))%I as "Hf".
      { iPureIntro. by rewrite Ha hom_vis. }
      iRewrite "Hf" in "H".
      rewrite {1}/internal_step. iSimpl in "H".
      iDestruct "H" as "[[H _]|H]".
      + iExFalso. iApply (IT_tick_vis_ne).
        iApply internal_eq_sym. done.
      + iDestruct "H" as (op' i' k') "[#Ha Hr]".
        iPoseProof (Vis_inj_op' with "Ha") as "<-".
        iPoseProof (Vis_inj' with "Ha") as "[Hi Hk]".
        iPoseProof (reify_input_cont_inv r op i k fi with "Hr") as (α') "[Hr Ha']".
        iAssert (reify r α σ ≡ (σ', Tick α', en))%I with "[Hr]" as "Hr".
        { iRewrite -"Hr". iPureIntro. repeat f_equiv.
          apply Ha. }
        iSplit. { iPureIntro. by rewrite Ha IT_to_V_Vis. }
        iExists α'. iFrame "Ha'".
        rewrite /internal_step. iRight.
        iExists op,i,k. iFrame "Hr".
        iPureIntro. apply Ha.
  Qed.
End internal_step_ctx_indep.
