From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import list.
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

  Global Instance tp_internal_steps'_ne : NonExpansive tp_internal_steps'.
  Proof.
    apply least_fixpoint_ne'.
    apply _.
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
