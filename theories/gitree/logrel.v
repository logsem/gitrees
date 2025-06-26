From iris.algebra Require Import excl auth frac agree gmap list gmap_view.
From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import base tactics classes modality_instances.
From iris.base_logic.lib Require Export own fancy_updates invariants mono_nat.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify greifiers reductions weakestpre lambda.
From gitrees Require Import hom.

Definition specN := nroot .@ "spec".
Definition stateN := nroot .@ "state".

Lemma take_drop_middle_L :
  ∀ {A : ofe} (l : list A) (i : nat) (x : A),
  l !! i ≡ Some x → take i l ++ x :: drop (S i) l ≡ l.
Proof.
  intros A l.
  induction l as [| x l Hl].
  - intros ?? H; simpl.
    exfalso.
    rewrite lookup_nil in H.
    inversion H.
  - intros i y H.
    simpl.
    destruct i as [| i].
    + simpl.
      rewrite drop_0.
      simpl in H.
      inversion H; subst.
      f_equiv; by symmetry.
    + simpl.
      f_equiv.
      simpl in H.
      by apply (Hl i y).
Qed.

Lemma lookup_lt_Some_L : ∀ {A : ofe} (l : list A) (i : nat) (x : A),
  l !! i ≡ Some x → i < length l.
Proof.
  intros ? l.
  induction l as [| y l Hl]; intros G.
  - intros ? J; inversion J.
  - intros x J.
    simpl.
    destruct G as [| G].
    + simpl in J.
      lia.
    + rewrite -Nat.succ_lt_mono.
      eapply Hl.
      apply J.
Qed.

Lemma lookup_geq_None_L : ∀ {A : ofe} (l : list A) (i : nat),
  l !! i ≡ None → i ≥ length l.
Proof.
  intros ? l.
  induction l as [| y l Hl]; intros G.
  - intros J; inversion J.
    simpl.
    lia.
  - intros J.
    simpl.
    destruct G as [| G].
    + simpl in J.
      inversion J.
    + simpl in J.
      apply Hl in J.
      lia.
Qed.

Lemma lookup_geq_None_L_inv : ∀ {A : ofe} (l : list A) (i : nat),
  i ≥ length l → l !! i = None.
Proof.
  intros ? l.
  induction l as [| y l Hl]; intros G.
  - intros J.
    done.
  - intros J.
    simpl in J.
    assert (∃ G', G = S G') as [G' ->].
    {
      inversion J as [ | J'].
      - exists (length l).
        lia.
      - exists J'.
        lia.
    }
    simpl.
    apply Hl.
    lia.
Qed.

Lemma tp_external_steps_many_L {a} {rs : sReifier a} `{!Cofe A}
  (α1 : listO (IT (sReifier_ops rs) A)) σ1 α2 σ2 α3 σ3 n2 :
  tp_external_step rs α2 σ2 α3 σ3 →
  tp_external_steps rs α1 σ1 α2 σ2 n2 →
  tp_external_steps rs α1 σ1 α3 σ3 (S n2).
Proof.
  intros G H; revert G.
  induction H as [| ??????????? IH]; intros G.
  - setoid_subst.
    econstructor 2; [| eassumption |]; last constructor 1; [| eassumption | |].
    + lia.
    + done.
    + done.
  - econstructor 2; [| eassumption |]; last by apply IH. lia.
Qed.

Lemma tp_internal_steps_many_L {a} {rs : sReifier a} `{!Cofe A}
  {Σ}
  (α1 : listO (IT (sReifier_ops rs) A)) σ1 α2 σ2 α3 σ3 n2 :
  ⊢ tp_internal_step (Σ := Σ) rs α2 σ2 α3 σ3
    -∗ tp_internal_steps rs α1 σ1 α2 σ2 n2
    -∗ tp_internal_steps rs α1 σ1 α3 σ3 (S n2).
Proof.
  iRevert (α1 σ1 α2 σ2 α3 σ3).
  iInduction n2 as [| n2 IH] "IH";
    iIntros (α1 σ1 α2 σ2 α3 σ3).
  - iIntros "G H".
    rewrite tp_internal_steps_0.
    iDestruct "H" as "(H1 & H2)".
    iRewrite "H1". iRewrite "H2".
    rewrite tp_internal_steps_S.
    iLeft.
    iExists α3, σ3.
    iSplit; first done.
    by rewrite tp_internal_steps_0.
  - iIntros "G H".
    iEval (rewrite tp_internal_steps_S) in "H".
    iDestruct "H" as "[H | H]".
    {
      iDestruct "H" as "(%γ & %σ' & H1 & H2)".
      iPoseProof ("IH" $! γ σ' α2 σ2 α3 σ3 with "G H2") as "J".
      iEval (rewrite tp_internal_steps_S).
      iLeft.
      iExists γ, σ'.
      by iSplit.
    }
    {
      iDestruct "H" as "(H1 & H2)".
      iRewrite "H1". iRewrite "H2".
      rewrite tp_internal_steps_unfold.
      iRight.
      iExists 0, α3, σ3.
      iSplit; first by (iPureIntro; lia).
      iFrame "G".
      rewrite tp_internal_steps_unfold.
      iLeft.
      iSplit; first by (iPureIntro; lia).
      done.
    }
Qed.

Lemma IT_tau_err_ne' `{Cofe R} {F} α e :
  (Tau (A := R) (E := F) α ≡ Err e → False).
Proof.
  intros H1.
  assert (IT_unfold (Tau α) ≡ IT_unfold (Err e)) as H2.
  { by rewrite H1. }
  rewrite !IT_unfold_fold /= in H2.
  inversion H2 as [?? G |]; subst.
  inversion G.
Qed.

Transparent Tau.
Lemma Tau_inj'' `{Cofe R} {F} (α β : laterO (IT F R)) :
  ((Tau α ≡ Tau β) → α ≡ β).
Proof.
  intros T.
  assert ((IT_unfold (Tau α)) ≡ (IT_unfold (Tau β))) as G.
  { rewrite T. done. }
  unfold Tau in G. simpl in G.
  rewrite !IT_unfold_fold in G.
  inversion G as [?? J |]; subst.
  inversion J; subst.
  done.
Qed.
Opaque Tau.

Lemma reify_vis_cont {rs : sReifier NotCtxDep} `{!Cofe R}
  op i k1 k2 σ1 σ2 β th :
  (reify (A := R) rs (Vis op i k1) σ1 ≡
     (σ2, Tick β, th) →
   reify rs (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡
     (σ2, Tick (k2 β), th)).
Proof.
  destruct (sReifier_re rs op (i,σ1))
    as [[[o σ2'] th']|] eqn:Hre; last first.
  - rewrite reify_vis_None_ctx_indep; last by rewrite Hre//.
    intros Hr.
    exfalso.
    destruct Hr as [[_ Hr2] _].
    simpl in Hr2.
    symmetry in Hr2.
    by apply IT_tau_err_ne' in Hr2.
  - rewrite reify_vis_eq_ctx_indep; last first.
    { by rewrite Hre. }
    rewrite reify_vis_eq_ctx_indep; last first.
    { by rewrite Hre. }
    intros Hr.
    destruct Hr as [[Hr1 Hr2] Hr3].
    simpl in *.
    rewrite Tick_eq in Hr2.
    rewrite Hr1.
    rewrite -Hr3.
    do 2 f_equiv.
    apply Tau_inj'' in Hr2.
    rewrite Hr2.
    rewrite later_map_Next.
    reflexivity.
Qed.

Lemma external_step_ectx {rs : sReifier NotCtxDep} `{!Cofe A}
  (K : HOM) (e : IT (sReifier_ops rs) A) e' σ σ' efs :
  external_step rs e σ e' σ' efs
  → external_step rs (K e) σ (K e') σ' efs.
Proof.
  intros H.
  destruct H as [???? H1 H2 | ???????? H1 H2].
  - rewrite H1 H2.
    rewrite hom_tick.
    by constructor.
  - rewrite H1.
    rewrite hom_vis.
    econstructor.
    + reflexivity.
    + assert (reify rs (Vis op i k) σ1 ≡ (σ2, Tick β, th))
        as J.
      {
        rewrite -H2.
        do 2 f_equiv.
        symmetry.
        done.
      }
      pose proof (reify_vis_cont op i k (λne x, K x) σ1 σ2 β th J) as L.
      simpl in J.
      rewrite -L.
      do 3 f_equiv.
      intros ?.
      reflexivity.
Qed.

Lemma external_step_ectx' {n} {rs : gReifiers NotCtxDep n} `{!Cofe A}
  (K : HOM) (e : IT (gReifiers_ops rs) A) e' σ σ' efs :
  external_step (gReifiers_sReifier rs) e σ e' σ' efs
  → external_step (gReifiers_sReifier rs) (K e) σ (K e') σ' efs.
Proof.
  intros H.
  destruct H as [???? H1 H2 | ???????? H1 H2].
  - rewrite H1 H2.
    rewrite hom_tick.
    by constructor.
  - rewrite H1.
    rewrite hom_vis.
    econstructor.
    + reflexivity.
    + assert (reify _ (Vis op i k) σ1 ≡ (σ2, Tick β, th))
        as J.
      {
        rewrite -H2.
        do 2 f_equiv.
        symmetry.
        done.
      }
      pose proof (reify_vis_cont op i k (λne x, K x) σ1 σ2 β th J) as L.
      simpl in J.
      rewrite -L.
      do 3 f_equiv.
      intros ?.
      reflexivity.
Qed.

Lemma tp_internal_steps_trans
  {a} {rs : sReifier a} `{!Cofe A} {Σ}
  (α1 : listO (IT (sReifier_ops rs) A)) σ1 α2 σ2 α3 σ3 n2 m2 :
  ⊢ tp_internal_steps (Σ := Σ) rs α2 σ2 α3 σ3 m2
    -∗ tp_internal_steps rs α1 σ1 α2 σ2 n2
    -∗ tp_internal_steps rs α1 σ1 α3 σ3 (m2 + n2).
Proof.
  iRevert (α1 σ1 α2 σ2 α3 σ3 n2).
  iInduction m2 as [| m2 IH] "IH";
    iIntros (α1 σ1 α2 σ2 α3 σ3 n2).
  - iIntros "G H".
    rewrite tp_internal_steps_0.
    iDestruct "G" as "(G1 & G2)".
    iRewrite - "G1". iRewrite - "G2".
    rewrite Nat.add_0_l.
    done.
  - iIntros "G H".
    iEval (rewrite tp_internal_steps_S) in "G".
    iDestruct "G" as "[G | G]".
    {
      iDestruct "G" as "(%γ & %σ' & G1 & G2)".
      rewrite Nat.add_succ_l -Nat.add_succ_r.
      iDestruct (tp_internal_steps_many_L with "G1 H") as "K".
      iApply ("IH" with "G2 K").
    }
    {
      iDestruct "G" as "(H1 & H2)".
      iRewrite - "H1". iRewrite - "H2".
      iApply (tp_internal_steps_grow with "H").
      lia.
    }
Qed.

Lemma tp_internal_steps_trans'
  {n} {rs : gReifiers NotCtxDep n} `{!Cofe A} {Σ}
  (α1 : listO (IT (gReifiers_ops rs) A)) σ1 α2 σ2 α3 σ3 n2 m2 :
  ⊢ tp_internal_steps (Σ := Σ) (gReifiers_sReifier rs) α2 σ2 α3 σ3 m2
    -∗ tp_internal_steps (gReifiers_sReifier rs) α1 σ1 α2 σ2 n2
    -∗ tp_internal_steps (gReifiers_sReifier rs) α1 σ1 α3 σ3 (m2 + n2).
Proof.
  iRevert (α1 σ1 α2 σ2 α3 σ3 n2).
  iInduction m2 as [| m2 IH] "IH";
    iIntros (α1 σ1 α2 σ2 α3 σ3 n2).
  - iIntros "G H".
    rewrite tp_internal_steps_0.
    iDestruct "G" as "(G1 & G2)".
    iRewrite - "G1". iRewrite - "G2".
    rewrite Nat.add_0_l.
    done.
  - iIntros "G H".
    iEval (rewrite tp_internal_steps_S) in "G".
    iDestruct "G" as "[G | G]".
    {
      iDestruct "G" as "(%γ & %σ' & G1 & G2)".
      rewrite Nat.add_succ_l -Nat.add_succ_r.
      iDestruct (tp_internal_steps_many_L with "G1 H") as "K".
      iApply ("IH" with "G2 K").
    }
    {
      iDestruct "G" as "(H1 & H2)".
      iRewrite - "H1". iRewrite - "H2".
      iApply (tp_internal_steps_grow with "H").
      lia.
    }
Qed.

Class monoSG Σ := MONOSG { mono_inG :: mono_natG Σ; mono_name : gname }.

Section steps.
  Context `{!monoSG Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own mono_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own mono_name n.

  Lemma steps_lb_0 :
    ⊢ |==> steps_lb 0.
  Proof. by apply mono_nat_lb_own_0. Qed.

  Local Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Local Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Local Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by iApply mono_nat_lb_own_le. Qed.

End steps.

Section tp.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Definition tpoolUR : ucmra := gmap_viewR nat (agreeR IT).

  Fixpoint to_tpool_go (i : nat) (tp : listO IT) : gmap nat (agreeR IT) :=
    match tp with
    | [] => ∅
    | e :: tp => <[i:=to_agree e]>(to_tpool_go (S i) tp)
    end.

  Lemma to_tpool_go_lookup (tp : listO IT) i :
    ∀ k j, to_tpool_go k tp !! j = to_tpool_go (k + i) tp !! (j + i).
  Proof.
    revert i.
    induction tp as [| ? tp IH].
    - done.
    - simpl.
      intros i k j.
      destruct (decide (k = j)); [subst |].
      + by rewrite !lookup_insert.
      + rewrite lookup_insert_ne; last done.
        rewrite (IH i (S k) j) /=.
        rewrite lookup_insert_ne; last lia.
        reflexivity.
  Qed.

  Lemma to_tpool_go_lookup' (tp : listO IT) :
    ∀ j k, to_agree <$> tp !! j = to_tpool_go k tp !! (k + j).
  Proof.
    induction tp as [| x tp IH].
    - intros ?; simpl.
      done.
    - intros j; simpl.
      destruct j as [| j].
      + simpl.
        intros k.
        rewrite Nat.add_0_r.
        destruct (decide (k = 0)); [subst |].
        * by rewrite lookup_insert.
        * by rewrite lookup_insert.
      + simpl.
        intros k.
        rewrite lookup_insert_ne; last lia.
        rewrite -Nat.add_succ_comm.
        rewrite -IH.
        reflexivity.
  Qed.

  Lemma to_tpool_go_comm_insert (tp : listO IT) j (H : j < length tp) x :
    to_tpool_go 0 (<[j := x]> tp) = <[j := to_agree x]> (to_tpool_go 0 tp).
  Proof.
    apply map_eq.
    intros q.
    rewrite -!(to_tpool_go_lookup' _ _ 0).
    destruct (decide (j = q)); [subst |].
    - rewrite lookup_insert.
      by rewrite list_lookup_insert; last done.
    - rewrite list_lookup_insert_ne; last done.
      rewrite lookup_insert_ne; last done.
      by rewrite (to_tpool_go_lookup' _ _ 0).
  Qed.

  Lemma to_tpool_go_comm_union (tp tp' : listO IT) :
    ∀ k, to_tpool_go k (tp ++ tp') = (to_tpool_go k tp) ∪ (to_tpool_go (k + length tp) tp').
  Proof.
    revert tp'.
    induction tp as [| ? ? IH].
    - intros; simpl.
      symmetry.
      rewrite Nat.add_0_r.
      apply (map_empty_union (to_tpool_go k tp')).
    - intros tp' k.
      rewrite /= IH Nat.add_succ_comm.
      by rewrite insert_union_l.
  Qed.

  Lemma to_tpool_go_map_to_list (tp : listO IT) :
    ∀ k, (map_to_list (to_tpool_go k tp)) ≡ₚ (zip (seq k (length tp)) (to_agree <$> tp)).
  Proof.
    induction tp as [| ? ? IH].
    - done.
    - intros k.
      rewrite /= -IH.
      rewrite map_to_list_insert; first done.
      replace (S k) with (1 + k) by reflexivity.
      assert (1 + k > k) as H; first lia.
      revert H.
      generalize (1 + k).
      generalize k.
      clear.
      induction tp as [| ? ? IH]; intros k p H.
      + done.
      + intros.
        rewrite /= lookup_insert_ne; last lia.
        apply IH; lia.
  Qed.

  Program Definition to_tpool' : listO IT -> tpoolUR := λ l, ●V (to_tpool_go 0 l).

  Program Definition to_tpool : listO IT -n> tpoolUR := λne l, (to_tpool' l).
  Next Obligation.
    rewrite /to_tpool'.
    intros p l.
    generalize 0.
    induction l as [| x l Hl]; intros m ? H.
    - apply Forall2_nil_inv_l in H.
      rewrite H.
      reflexivity.
    - apply Forall2_cons_inv_l in H.
      destruct H as [x' [l' [H1 [H2 H3]]]].
      rewrite H3.
      simpl.
      do 2 f_equiv.
      + solve_proper.
      + specialize (Hl (S m) l' H2).
        destruct Hl as [Hl _].
        simpl in Hl.
        apply Some_dist_inj in Hl.
        apply pair_dist_inj in Hl.
        destruct Hl as [_ Hl].
        apply to_agree_injN in Hl.
        apply Hl.
  Qed.

  Class tpoolSG Σ := TPOOLSG { tpool_inG :: inG Σ ( tpoolUR); tpool_name : gname }.
End tp.

Section right_hand_side.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context {Σ : gFunctors}.
  Context `(HSTATE : !stateG rs R Σ).
  Context `{!invGS_gen HasLc Σ} `{!tpoolSG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Program Definition tpool_pointsto (j : natO) (e : IT) : iProp :=
    own (tpool_name rs R) (gmap_view_frag j (DfracOwn 1) (to_agree e)).

  Global Instance tpool_pointsto_ne l : NonExpansive (tpool_pointsto l).
  Proof.
    intros ??? H.
    rewrite /tpool_pointsto.
    do 3 f_equiv.
    done.
  Qed.

  Global Instance tpool_pointsto_proper l : Proper ((≡) ==> (≡)) (tpool_pointsto l).
  Proof.
    intros ?? H.
    rewrite /tpool_pointsto.
    do 3 f_equiv.
    apply H.
  Qed.

  Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.

  Program Definition spec_inv (ρ : listO IT) σ : iProp :=
    (∃ tp σ' m, own (tpool_name rs R) ((to_tpool rs R tp))
                ∗ @state_interp _ _ _ _ _ _ HSTATE σ'
                ∗ tp_internal_steps (gReifiers_sReifier rs) ρ σ tp σ' m)%I.

  Definition spec_ctx : iProp :=
    (∃ ρ σ, inv specN (spec_inv ρ σ))%I.

  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.

  Lemma step_insert (K : HOM) (tp : listO IT) j e σ e' σ' efs :
    tp !! j ≡ Some (K e) → external_step (gReifiers_sReifier rs) e σ e' σ' efs →
    tp_external_step (gReifiers_sReifier rs) tp σ (<[j:=K e']> tp ++ efs) σ'.
  Proof.
    intros.
    rewrite -(take_drop_middle_L tp j (K e)) //.
    rewrite insert_app_r_alt; first last.
    {
      rewrite length_take_le; first reflexivity.
      apply Nat.lt_le_incl.
      eapply lookup_lt_Some_L; eassumption.
    }
    econstructor.
    - reflexivity.
    - rewrite -assoc_L.
      f_equiv.
      rewrite length_take_le; first last.
      {
        apply Nat.lt_le_incl.
        eapply lookup_lt_Some_L.
        eassumption.
      }
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    -
      by apply external_step_ectx'.
  Qed.

  Lemma step_insert_no_fork (K : HOM) (tp : listO IT) j e σ e' σ' :
    tp !! j ≡ Some (K e) → external_step (gReifiers_sReifier rs) e σ e' σ' [] →
    tp_external_step (gReifiers_sReifier rs) tp σ (<[j:=K e']> tp) σ'.
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma tpool_read l α tp :
    own (tpool_name rs R) (to_tpool rs R tp)
    -∗ tpool_pointsto l α
    -∗ (tp !! l) ≡ Some α.
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[%H Hval]".
    rewrite option_equivI.
    rewrite -(to_tpool_go_lookup' rs R tp l 0).
    destruct (tp !! l) as [o |] eqn:Heq.
    - rewrite Heq /=.
      rewrite agree_equivI.
      iDestruct "Hval" as "(_ & Hval)".
      by iRewrite "Hval".
    - rewrite Heq /=.
      iDestruct "Hval" as "(_ & Hval)".
      done.
  Qed.

  Lemma tpool_alloc α l σ :
    σ !! l = None →
    own (tpool_name rs R) (to_tpool rs R σ)
    ==∗ own (tpool_name rs R) (●V (<[l:=to_agree (α)]>(to_tpool_go rs R 0 σ)))
                   ∗ tpool_pointsto l α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { apply (gmap_view_alloc _ l (DfracOwn 1) (to_agree (α))); eauto.
      - rewrite -(to_tpool_go_lookup' rs R σ l 0).
        by rewrite Hl.
      - done.
      - done.
    }
    done.
  Qed.

  Lemma tpool_alloc_big (α : listO IT) σ :
    own (tpool_name rs R) (to_tpool rs R σ)
    ==∗ own (tpool_name rs R)
          (●V ((to_tpool_go rs R 0 σ) ∪ (to_tpool_go rs R (length σ) α)))
                   ∗ [∗ list] i ∈ α, ∃ j, tpool_pointsto j i.
  Proof.
    iIntros "H".
    assert (∀ k, to_tpool_go rs R (k + (length σ)) α ##ₘ to_tpool_go rs R k σ) as HD.
    {
      induction σ as [| x σ IH].
      - intros; apply map_disjoint_empty_r.
      - intros k; simpl.
        apply map_disjoint_insert_r_2.
        + rewrite Nat.add_comm.
          rewrite -(to_tpool_go_lookup rs R α k (S (length σ)) 0).
          clear.
          generalize (length σ).
          induction α as [| ? ? IH].
          * done.
          * intros m; simpl.
            rewrite lookup_insert_ne; last done.
            apply IH.
        + rewrite -Nat.add_1_l Nat.add_assoc (Nat.add_comm k).
          apply IH.
    }
    iMod (own_update with "H") as "[H1 H2]".
    {
      specialize (HD 0).
      simpl in HD.
      apply (gmap_view_alloc_big (to_tpool_go rs R 0 σ)
                     (to_tpool_go rs R (length σ) α)
                     (DfracOwn 1) HD); eauto.
      - done.
      - apply map_Forall_lookup_2.
        intros i x H.
        clear -H.
        revert H.
        generalize (length σ).
        clear.
        induction α as [| ? ? IH]; intros l H.
        + inversion H.
        + simpl in H.
          destruct (decide (l = i)); first subst.
          * rewrite lookup_insert in H.
            inversion H; subst.
            done.
          * rewrite lookup_insert_ne in H; last done.
            by eapply IH.
    }
    rewrite map_union_comm; last apply (HD 0).
    iModIntro.
    iSplitL "H1".
    - unfold gmap_view_auth. (* wtf ??? *)
      iFrame "H1".
    - unfold tpool_pointsto.
      clear.
      generalize (length σ).
      intros p.
      iInduction α as [| ??] "IH" forall (p).
      + done.
      + simpl.
        rewrite big_opM_insert.
        * iDestruct "H2" as "(H2 & H3)".
          iSplitL "H2".
          -- by iExists p.
          -- iApply "IH".
             iApply "H3".
        * replace (S p) with (1 + p) by reflexivity.
          assert (1 + p > p) as H; first lia.
          revert H.
          generalize (1 + p).
          generalize p.
          clear.
          induction α as [| ? ? IH]; intros k p H.
          -- done.
          -- intros.
             rewrite /= lookup_insert_ne; last lia.
             apply IH; lia.
  Qed.

  Lemma tpool_loc_dom l α tp :
    own (tpool_name rs R) (to_tpool rs R tp)
    -∗ tpool_pointsto l α -∗ ⌜is_Some (tp !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (tpool_read with "Hinv Hloc") as "Hl".
    destruct (tp !! l) ; eauto.
    by rewrite option_equivI.
  Qed.

  Lemma tpool_write l α β σ :
    own (tpool_name rs R) (to_tpool rs R σ)
    -∗ tpool_pointsto l α
    ==∗ own (tpool_name rs R) (●V <[l:=(to_agree (β))]>(to_tpool_go rs R 0 σ))
      ∗ tpool_pointsto l β.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]"; last done.
    by apply gmap_view_replace.
  Qed.

  Lemma step_tick E j e :
    nclose specN ⊆ E →
    £ 1 ∗ spec_ctx ∗ ▷ j ⤇ Tick e ={E}=∗ j ⤇ e.
  Proof.
    iIntros (HSub) "[HCred [#HSpec HPt]]".
    iDestruct "HSpec" as (tp σ) "HSpec".
    iInv specN as "H" "HClose".
    iApply (lc_fupd_add_later with "HCred").
    iNext.
    iDestruct "H" as (tp' σ' m) "[H [HS #HStep]]".
    iAssert (⌜is_Some (tp' !! j)⌝)%I as "%Hdom".
    { iApply (tpool_loc_dom with "H HPt"). }
    destruct Hdom as [x Hx].
    iAssert ((tp' !! j ≡ Some (Tick e)))%I as "#Hlookup".
    { iApply (tpool_read with "H HPt"). }
    iMod (tpool_write _ _ e with "H HPt") as "[Hh Hp]".
    iMod ("HClose" with "[HS Hh]") as "_"; last by iModIntro.
    iNext.
    iExists (<[j:=e]> tp'), σ', (S m).
    iFrame "HS".
    iSplit; first last.
    - iApply tp_internal_steps_many_L; last done.
      unshelve epose proof (take_drop_middle tp' j x _) as H; first by rewrite Hx.
      rewrite -H.
      rewrite list_lookup_middle; first last.
      {
        rewrite length_take_le; first done.
        eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
      }
      iDestruct (option_equivI with "Hlookup") as "G".
      iRewrite "G".
      iExists (take j tp'), (drop (S j) tp'), (Tick e), e, [].
      iSplit; first done.
      iSplit.
      {
        rewrite insert_app_r_alt; last (rewrite length_take; lia).
        rewrite app_nil_r.
        iApply f_equivI.
        assert (j - length (take j tp') = 0) as ->.
        {
          rewrite length_take_le; first lia.
          eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
        }
        simpl.
        done.
      }
      iLeft.
      done.
    - rewrite /to_tpool /= /to_tpool'.
      rewrite to_tpool_go_comm_insert; first done.
      eapply lookup_lt_Some; eassumption.
  Qed.

  Lemma step_reify
    `{subR : !subReifier sR rs}
    E j
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l :
    nclose specN ⊆ E →
    £ 1
    ∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
    ∗ k (subEff_outs y) ≡ Next β
    ∗ spec_ctx
    ∗ ▷ has_substate σ
    ∗ ▷ j ⤇ (Vis (subEff_opid op) (subEff_ins x) k)
    ={E}=∗ j ⤇ β
         ∗ ([∗ list] i ∈ listO_map Tau l, ∃ j0 : natO, j0 ⤇ i)
         ∗ has_substate σ'.
  Proof.
    iIntros (HSub) "(HCred & #Hr & #HEq & #HSpec & HSt & HPt)".
    iDestruct "HSpec" as (tp σ'') "HSpec".
    iInv specN as "H" "HClose".
    iApply (lc_fupd_add_later with "HCred").
    iNext.
    iDestruct "H" as (tp' σ''' m) "[H [HS #HStep]]".
    iAssert (⌜is_Some (tp' !! j)⌝)%I as "%Hdom".
    { iApply (tpool_loc_dom with "H HPt"). }
    destruct Hdom as [x' Hx].
    iAssert ((tp' !! j ≡ Some (Vis (subEff_opid op) (subEff_ins x) k)))%I
      as "#Hlookup".
    { iApply (tpool_read with "H HPt"). }
    iMod (tpool_write _ _ β
           with "H HPt") as "[Hh Hp]".
    iMod (tpool_alloc_big (listO_map Tau l) (<[j := β]>tp') with "[Hh]") as "[Hh Hpool]".
    {
      rewrite /to_tpool /to_tpool' /=.
      rewrite to_tpool_go_comm_insert; first done.
      apply lookup_lt_is_Some_1.
      eexists _; eassumption.
    }
    destruct (gState_decomp sR_idx σ''') as [a rest] eqn:Hdecomp.
    assert (σ''' ≡ gState_recomp rest a) as Hfs.
    { symmetry. apply gState_recomp_decomp. by rewrite Hdecomp. }
    iAssert (a ≡ (sR_state σ))%I with "[HS HSt]" as "#Hss".
    {
      iEval (rewrite Hfs) in "HS".
      iApply (state_interp_has_state_idx_agree with "HS HSt").
    }
    iAssert (internal_step (gReifiers_sReifier rs)
               ((Vis (subEff_opid op) (subEff_ins x) k)) σ'''
               β (gState_recomp rest (sR_state σ')) (listO_map Tau l)) as "HStep'".
    {
      iRight.
      iExists (subEff_opid op), (subEff_ins x), k.
      iSplit; first done.
      rewrite Tick_eq.
      iDestruct (reify_vis_eqI_ctx_indep rs
                     (subEff_opid op) (subEff_ins x) k
                     (subEff_outs y) (gState_recomp rest (sR_state σ))
                     (gState_recomp rest (sR_state σ')) l
                  with "[]") as "Hreify".
      {
        iApply subReifier_reifyI_ctx_indep.
        iApply "Hr".
      }
      iRewrite "HEq" in "Hreify".
      setoid_replace σ''' with (gState_recomp rest a); last done.
      iRewrite "Hss".
      iApply "Hreify".
    }
    iEval (rewrite Hfs) in "HS".
    iMod (state_interp_has_state_idx_update _ (sR_state σ') with "HS HSt") as "[HS HSt]".
    iFrame "Hp Hpool HSt".
    iApply "HClose".
    iNext.
    iExists (<[j := β]>tp' ++ (listO_map Tau l)),
      (gState_recomp rest (sR_state σ')), (S m).
    iSplitL "Hh".
    - rewrite /to_tpool /to_tpool'.
      rewrite -to_tpool_go_comm_union /=.
      iFrame "Hh".
    - iFrame "HS".
      iApply tp_internal_steps_many_L; last done.
      unshelve epose proof (take_drop_middle tp' j x' _) as H; first done.
      rewrite -H; clear H.
      rewrite list_lookup_middle; first last.
      {
        rewrite length_take_le; first done.
        eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
      }
      iDestruct (option_equivI with "Hlookup") as "G".
      iRewrite "G"; iClear "G".

      iExists (take j tp'), (drop (S j) tp'), (Vis (subEff_opid op) (subEff_ins x) k), (β), (listO_map Tau l).
      iSplit; first done.
      iSplit.
      {
        rewrite insert_app_r_alt; last (rewrite length_take; lia).
        rewrite -app_assoc.
        iApply f_equivI.
        assert (j - length (take j tp') = 0) as ->.
        {
          rewrite length_take_le; first lia.
          eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
        }
        simpl.
        done.
      }
      iApply "HStep'".
  Qed.

  Lemma step_reify_hom
    `{subR : !subReifier sR rs}
    (K : HOM) E j
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l :
    nclose specN ⊆ E →
    £ 1
    ∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
    ∗ k (subEff_outs y) ≡ Next β
    ∗ spec_ctx
    ∗ ▷ has_substate σ
    ∗ ▷ j ⤇ K (Vis (subEff_opid op) (subEff_ins x) k)
    ={E}=∗ j ⤇ K β
         ∗ ([∗ list] i ∈ listO_map Tau l, ∃ j0 : natO, j0 ⤇ i)
         ∗ has_substate σ'.
  Proof.
    iIntros (HSub) "(HCred & #Hr & #HEq & #HSpec & HSt & HPt)".
    rewrite hom_vis.
    iDestruct (step_reify with "[Hr HEq $HSpec $HCred $HSt HPt]") as "H";
      first done.
    - iFrame "HPt".
      iFrame "Hr".
      rewrite /=.
      iRewrite "HEq".
      rewrite later_map_Next.
      done.
    - iApply "H".
  Qed.

  Lemma step_steps E j (e e' : IT) P σ σ' l m :
    nclose specN ⊆ E →
    ▷ P
    ∗ £ 1
    ∗ spec_ctx
    ∗ ▷ has_full_state σ
    ∗ internal_steps (gReifiers_sReifier rs) e σ e' σ' l m
    ∗ ▷ j ⤇ e
    ={E}=∗ P
         ∗ j ⤇ e'
         ∗ ([∗ list] i ∈ l, ∃ k : natO, k ⤇ i)
         ∗ has_full_state σ'.
  Proof.
    iIntros (HSub) "(P & HCred & #Hspec & Hstate & #HSteps & HPt)".
    iDestruct "Hspec" as (tp st) "Hspec".
    iInv specN as "H" "HClose".
    iApply (lc_fupd_add_later with "HCred").
    iNext.
    iDestruct "H" as (tp' st' p) "[H [HS #HSteps']]".
    iAssert (⌜is_Some (tp' !! j)⌝)%I as "%Hdom".
    { iApply (tpool_loc_dom with "H HPt"). }
    destruct Hdom as [x' Hx].
    iAssert ((tp' !! j ≡ Some e))%I
      as "#Hlookup".
    { iApply (tpool_read with "H HPt"). }
    iAssert (st' ≡ σ)%I with "[HS Hstate]" as "#Hss".
    { iApply (state_interp_has_full_state_agree with "HS Hstate"). }
    iRewrite "Hss" in "HSteps'"; iRewrite "Hss" in "HS"; iRewrite "Hss" in "HClose";
      iClear "Hss"; clear st'.
    iAssert (e ≡ x')%I as "HEQ".
    {
      rewrite Hx.
      iDestruct (internal_eq_sym with "Hlookup") as "Hlookup'".
      iApply (option_equivI with "Hlookup'").
    }
    iRewrite "HEQ" in "HPt"; iRewrite "HEQ" in "HSteps";
      iClear "Hlookup HEQ"; clear e.
    iMod (tpool_write _ _ e' with "H HPt") as "[H HPt]".
    iMod (tpool_alloc_big l (<[j := e']>tp') with "[H]") as "[H Hpool]".
    {
      rewrite /to_tpool /to_tpool' /=.
      rewrite to_tpool_go_comm_insert; first done.
      apply lookup_lt_is_Some_1.
      eexists _; eassumption.
    }
    iMod (state_interp_has_full_state_update σ' with "HS Hstate")
      as "[HS Hstate]".
    iFrame "HPt Hpool Hstate P".
    iApply "HClose".
    iExists (<[j := e']>tp' ++ l), σ', (p + m).
    iFrame "HS".
    rewrite /to_tpool /to_tpool'.
    rewrite -to_tpool_go_comm_union.
    iFrame "H".
    iNext.
    unshelve epose proof (take_drop_middle tp' j x' _) as H; first done.
    rewrite -H; clear H.
    iPoseProof (internal_steps_tp_internal_steps with "HSteps") as "K".
    iPoseProof (tp_internal_steps_trans with "K HSteps'") as "J".
    iEval (rewrite Nat.add_comm).
    iEval (rewrite insert_app_r_alt; last (rewrite length_take; lia)).
    iEval (rewrite -app_assoc).
    assert (j - length (take j tp') = 0) as ->.
    {
      rewrite length_take_le; first lia.
      eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
    }
    iApply "J".
  Qed.

  Lemma step_steps_not_stateful P E j
    (e e' : IT) l m :
    nclose specN ⊆ E →
    ▷ P
    ∗ £ 1
    ∗ spec_ctx
    ∗ (∀ σ, internal_steps (gReifiers_sReifier rs) e σ e' σ l m)
    ∗ ▷ j ⤇ e
    ={E}=∗ P
         ∗ j ⤇ e'
         ∗ ([∗ list] i ∈ l, ∃ k : natO, k ⤇ i).
  Proof.
    iIntros (HSub) "(P & HCred & #Hspec & #HSteps & HPt)".
    iDestruct "Hspec" as (tp st) "Hspec".
    iInv specN as "H" "HClose".
    iApply (lc_fupd_add_later with "HCred").
    iNext.
    iDestruct "H" as (tp' st' p) "[H [HS #HSteps']]".
    iAssert (⌜is_Some (tp' !! j)⌝)%I as "%Hdom".
    { iApply (tpool_loc_dom with "H HPt"). }
    destruct Hdom as [x' Hx].
    iAssert ((tp' !! j ≡ Some e))%I
      as "#Hlookup".
    { iApply (tpool_read with "H HPt"). }
    iSpecialize ("HSteps" $! st').
    iAssert (e ≡ x')%I as "HEQ".
    {
      rewrite Hx.
      iDestruct (internal_eq_sym with "Hlookup") as "Hlookup'".
      iApply (option_equivI with "Hlookup'").
    }
    iRewrite "HEQ" in "HPt"; iRewrite "HEQ" in "HSteps";
      iClear "Hlookup HEQ"; clear e.
    iMod (tpool_write _ _ e' with "H HPt") as "[H HPt]".
    iMod (tpool_alloc_big l (<[j := e']>tp') with "[H]") as "[H Hpool]".
    {
      rewrite /to_tpool /to_tpool' /=.
      rewrite to_tpool_go_comm_insert; first done.
      apply lookup_lt_is_Some_1.
      eexists _; eassumption.
    }
    iFrame "HPt Hpool P".
    iApply "HClose".
    iExists (<[j := e']>tp' ++ l), st', (p + m).
    iFrame "HS".
    rewrite /to_tpool /to_tpool'.
    rewrite -to_tpool_go_comm_union.
    iFrame "H".
    iNext.
    unshelve epose proof (take_drop_middle tp' j x' _) as H; first done.
    rewrite -H; clear H.
    iPoseProof (internal_steps_tp_internal_steps with "HSteps") as "K".
    iPoseProof (tp_internal_steps_trans with "K HSteps'") as "J".
    iEval (rewrite Nat.add_comm).
    iEval (rewrite insert_app_r_alt; last (rewrite length_take; lia)).
    iEval (rewrite -app_assoc).
    assert (j - length (take j tp') = 0) as ->.
    {
      rewrite length_take_le; first lia.
      eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
    }
    iApply "J".
  Qed.

End right_hand_side.

Notation "j ⤇ e" := (tpool_pointsto _ _ j e) (at level 20) : bi_scope.

Section rel.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context {Σ : gFunctors}.
  Context `(HSTATE : !stateG rs R Σ).
  Context `{!gitreeGS_gen rs R Σ} `{!tpoolSG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Program Definition IT_Rel_pre
    (IT_Val_Rel : ITV -n> ITV -n> iProp)
    : IT -> IT -> iProp
    := λ x y,
      (∀ j (K : HOM), j ⤇ K y
              -∗ WP@{rs} x @ s {{ v,
                       ∃ v', j ⤇ K (IT_of_V v')
                             ∗ IT_Val_Rel v v' }})%I.

  Global Instance IT_Rel_pre_ne : NonExpansive3 IT_Rel_pre.
  Proof.
    intros ??? H1 ?? H2 ?? H3.
    rewrite /IT_Rel_pre.
    do 2 (f_equiv; intros ?).
    f_equiv; first solve_proper.
    f_equiv; first solve_proper.
    intros ?; simpl.
    f_equiv; intros ?.
    f_equiv; solve_proper.
  Qed.

  Global Instance IT_Rel_pre_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) IT_Rel_pre.
  Proof.
    intros ?? H1 ?? H2 ?? H3.
    rewrite /IT_Rel_pre.
    do 2 (f_equiv; intros ?).
    f_equiv; first solve_proper.
    f_equiv; first solve_proper.
    intros ?; simpl.
    f_equiv; intros ?.
    f_equiv; solve_proper.
  Qed.

  Program Definition IT_Val_Rel_pre (R : ITV -n> ITV -n> iProp) :
    ITV -n> ITV -n> iProp
    := λne x y,
      ((∃ a b, IT_of_V x ≡ core.Ret a
               ∧ IT_of_V y ≡ core.Ret b
               ∧ a ≡ b)
       ∨ (∃ f g, IT_of_V x ≡ Fun f
                 ∧ IT_of_V y ≡ Fun g
                 ∧ □ ∀ v w,
            ▷ (R v w
               -∗ IT_Rel_pre R
                    (APP' (IT_of_V x) (IT_of_V v))
                    (APP' (IT_of_V y) (IT_of_V w)))))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  Global Instance IT_Val_Rel_pre_contractive : Contractive IT_Val_Rel_pre.
  Proof.
    intros m ?? H.
    rewrite /IT_Val_Rel_pre.
    intros ??; simpl.
    do 4 f_equiv.
    intros ?; simpl.
    do 3 f_equiv.
    do 2 (f_equiv; intros ?).
    apply later_contractive.
    destruct m as [| m].
    - apply dist_later_0.
    - apply dist_later_S.
      f_equiv.
      + apply dist_later_S in H.
        solve_proper.
      + do 1 (f_equiv; intros ?).
        apply dist_later_S in H.
        solve_proper.
  Qed.

  Program Definition IT_Val_Rel : ITV -n> ITV -n> iProp := fixpoint IT_Val_Rel_pre.

  Lemma IT_Val_Rel_unfold' : IT_Val_Rel ≡ IT_Val_Rel_pre IT_Val_Rel.
  Proof. apply fixpoint_unfold. Qed.

  Program Definition IT_Rel := IT_Rel_pre IT_Val_Rel.

  Lemma IT_Val_Rel_unfold v' w'
    : IT_Val_Rel v' w' ≡
        ((∃ a b, IT_of_V v' ≡ core.Ret a
                 ∧ IT_of_V w' ≡ core.Ret b
                 ∧ a ≡ b)
         ∨ (∃ f g, IT_of_V v' ≡ Fun f
                   ∧ IT_of_V w' ≡ Fun g
                   ∧ □ ∀ v w,
              ▷ (IT_Val_Rel v w
                 -∗ IT_Rel
                      (APP' (IT_of_V v') (IT_of_V v))
                      (APP' (IT_of_V w') (IT_of_V w)))))%I.
  Proof.
    rewrite (IT_Val_Rel_unfold' v' w') /IT_Val_Rel_pre //=.
  Qed.

  Global Instance IT_Val_Rel_persist e1 e2 : Persistent (IT_Val_Rel e1 e2).
  Proof.
    rewrite IT_Val_Rel_unfold /IT_Val_Rel_pre.
    apply _.
  Qed.

  Global Instance IT_Rel_proper : Proper ((≡) ==> (≡) ==> (≡)) IT_Rel.
  Proof. solve_proper. Qed.

  Global Instance IT_Rel_ne : NonExpansive2 IT_Rel.
  Proof. solve_proper. Qed.

  Global Instance IT_Val_Rel_proper1 : Proper ((≡) ==> (≡)) IT_Val_Rel.
  Proof. solve_proper. Qed.

  Global Instance IT_Val_Rel_proper2 a : Proper ((≡) ==> (≡)) (IT_Val_Rel a).
  Proof. solve_proper. Qed.

  Global Instance IT_Val_Rel_ne1 : NonExpansive IT_Val_Rel.
  Proof. solve_proper. Qed.

  Global Instance IT_Val_Rel_ne2 a : NonExpansive (IT_Val_Rel a).
  Proof. solve_proper. Qed.

  Definition IT_Top_Rel e1 e2 : iProp :=
    spec_ctx rs _ HSTATE → IT_Rel e1 e2.

  Global Instance IT_Top_Rel_proper : Proper ((≡) ==> (≡) ==> (≡)) IT_Top_Rel.
  Proof. solve_proper. Qed.

  Global Instance IT_Top_Rel_ne : NonExpansive2 IT_Top_Rel.
  Proof. solve_proper. Qed.
End rel.

Notation "e1 ⪯ₑ e2 '@{' re \ A \ s '}'" :=
  (IT_Rel re A s e1 e2) (at level 80) : bi_scope.
Notation "e1 ⪯ᵥ e2 '@{' re \ A \ s '}'" :=
  (IT_Val_Rel re A s e1 e2) (at level 80) : bi_scope.
Notation "e1 ⪯ₚ e2 '@{' re \ A \ s \ H '}'" :=
  (IT_Top_Rel re A H s e1 e2) (at level 80) : bi_scope.

Lemma logrel_adequacy_internal Σ cr n
  (rs : gReifiers NotCtxDep n)
  {A} `{!Cofe A} `{!invGpreS Σ}
  `{!Inhabited (gReifiers_state rs ♯ IT (sReifier_ops (gReifiers_sReifier rs)) A)}
  `{!statePreG rs A Σ} `{!inG Σ (tpoolUR rs A)}
  (α β : IT _ A) σ αv αs σ' (s : stuckness) k :

  let rg := gReifiers_sReifier rs in
  let F := sReifier_ops rg in
  let IT := IT F A in
  let ITV := ITV F A in

  tp_external_steps rg [α] σ (IT_of_V αv :: αs) σ' k →
  (∀ `{H1 : !gitreeGS_gen rs A Σ} `{!tpoolSG rs A Σ} `{HSTATE : !stateG rs A Σ},
     (⊢@{iProp Σ} (£ cr
                   -∗ @has_full_state _ _ rs _ _ _ HSTATE σ
                   -∗ (α) ⪯ₚ (β) @{ rs \ A \ s \ HSTATE })%I)) →
  ⊢@{iProp Σ} (∃ αv βs st' k', tp_internal_steps (gReifiers_sReifier rs) [β] σ
                              (IT_of_V αv :: βs) st' k').
Proof.
  intros rg F IT' ITV' Hsteps Hprf.
  apply (step_fupdN_soundness_lc _ (S (weakestpre.steps_sum id 0 k))
                     ((weakestpre.steps_sum id 0 k) + (S cr))).

  iIntros (H1) "(_HCred' & (_HCred & _HCred''))".
  iMod (new_state_interp σ) as (H2) "[Hs Hs2]".
  assert (G1 : (nat → ∀ σ, state_interp σ
                           ⊢ |={∅}=> state_interp σ)).
  { intros. iIntros "?". by iModIntro. }
  assert (G2 : (nat → NonExpansive (λ σ, state_interp σ)%I)).
  { solve_proper. }
  assert (G3 : (nat → ∀ σ, state_interp σ
                           ⊣⊢ True ∗ state_interp σ)).
  {
    intros. iSplit; iIntros "H".
    - by iFrame "H".
    - by iDestruct "H" as "(_ & ?)".
  }
  pose GGS : gitreeGS_gen rs A Σ :=
    GitreeG rs A Σ H1 H2
      (λ n σ, @state_interp _ _ rs A _ _ H2 σ)%I
      (λ _, True%I)
      (λ _, True%I)
      ltac:(solve_proper)
      id
      G1
      G2
      G3.
  iMod (new_state_interp σ) as (sg') "[Hs' Hsfull']".
  iMod (own_alloc ((to_tpool rs A []))) as (γ) "Ht".
  { by apply gmap_view_auth_dfrac_valid. }
  set (T := {| tpool_inG := _; tpool_name := γ |} : tpoolSG rs A Σ).
  iPoseProof (Hprf GGS T sg') as "#H". clear Hprf.
  iDestruct (tp_external_steps_tp_internal_steps _ _ _ _ _ _ Hsteps) as "Hsteps".
  iSpecialize ("H" with "_HCred'' Hsfull'").
  iMod (tpool_alloc rs A β 0 with "[$Ht]") as "(Ht & Hp)"; first done.
  iMod (inv_alloc specN _ (spec_inv rs A sg' [β] σ)
         with "[Hs' Ht]") as "#Hinv".
  {
    iNext.
    unfold spec_inv.
    iExists [β], σ, 0.
    iFrame "Ht Hs'".
    by iApply tp_internal_steps_0.
  }
  iAssert (spec_ctx rs A sg') with "[]" as "G".
  { iExists [β], σ. iFrame "Hinv". }
  iSpecialize ("H" with "G").
  iSpecialize ("H" $! 0 HOM_id with "Hp").
  set (Φs := [(λ v, ∃ v', (0 ⤇ idfun (IT_of_V v')
                           ∗ IT_Val_Rel _ _ s v v') ∗ £ 1)%I]).
  assert (Forall (λ f : ITV (sReifier_ops (gReifiers_sReifier rs)) A → iProp Σ,
                NonExpansive f) Φs) as HEΦs.
  {
    apply Forall_singleton.
    solve_proper_prepare.
    f_equiv. intros ?; simpl.
    f_equiv. f_equiv. f_equiv.
    f_equiv.
    done.
  }
  iMod (wptp_postconditions
                rs Φs HEΦs s k _ _ _ 0 _
              with "Hsteps [Hs] [_HCred'] [H _HCred]") as "J".
  { iSimpl. iApply "Hs". }
  { iSimpl. iApply "_HCred'". }
  {
    rewrite /wptp big_sepL2_singleton.
    iApply (wp_wand with "H").
    iIntros (v) "_G".
    iModIntro.
    iDestruct "_G" as (v') "_G".
    iExists v'.
    iFrame "_G _HCred".
  }
  rewrite step_fupdN_S_fupd.
  iModIntro.
  iApply (step_fupdN_wand with "J").
  iModIntro. iNext. iModIntro.
  iIntros "J".
  iMod "J".
  subst Φs.
  iSimpl in "J".
  iDestruct "J" as (nt') "(HS & H1 & _)".
  match goal with
  | |- context G [from_option ?a] =>
      set (Φ := a)
  end.
  iDestruct (internal_eq_rewrite (IT_to_V (IT_of_V αv))
               (Some αv)
               (from_option Φ True%I) with "[] H1") as "H1".
  { subst Φ. solve_proper. }
  { iPureIntro. rewrite IT_to_of_V. done. }
  subst Φ. iSimpl in "H1".
  iDestruct "H1" as (v') "((Hpt & Hrel) & HCred)".
  iInv specN as (tp σ'' m) "(J1 & J2 & #J3)" "HClose".
  iClear "Hinv G".
  iApply (lc_fupd_add_later with "HCred").
  iNext.
  iPoseProof (tpool_loc_dom with "J1 Hpt") as "%K".
  iAssert (⌜∃ αv βs, tp ≡ IT_of_V αv :: βs⌝)%I with "[J1 Hpt]" as "%K'".
  {
    iPoseProof (tpool_read with "J1 Hpt") as "K".
    destruct tp as [| o tp'].
    - exfalso.
      destruct K as [? K].
      inversion K.
    - iSimpl in "K".
      iDestruct (option_equivI with "K") as "K".
      destruct v'.
      + iSimpl in "K".
        iDestruct (ret_discrete_pure (gReifiers_sReifier rs) o o0 with "K") as (β') "%J".
        iExists (core.RetV β'), tp'.
        iPureIntro. simpl.
        by rewrite J.
      + iSimpl in "K".
        iDestruct (fun_discrete_pure (gReifiers_sReifier rs) o o0 with "K") as (β') "%J".
        iExists (core.FunV β'), tp'.
        iPureIntro. simpl.
        by rewrite J.
  }
  destruct K' as [? [? HEQ]].
  iAssert (▷ spec_inv rs A sg' [β] σ)%I with "[J2 J1]" as "JJJ".
  {
    iNext.
    unfold spec_inv.
    iExists tp, σ'', m.
    iFrame "J3 J2 J1".
  }
  iSpecialize ("HClose" with "JJJ").
  iMod "HClose".
  iAssert (tp_internal_steps (gReifiers_sReifier rs) [β] σ
             (IT_of_V x :: x0) σ'' m)%I as "J3'".
  {
    rewrite /tp_internal_steps /=.
    by rewrite -HEQ.
  }
  iApply fupd_mask_intro; first done.
  iIntros "_".
  iExists x, x0, σ'', m.
  iFrame "J3'".
Qed.

Lemma internal_steps_bounding_fun_witness (AC : Choice) Σ {a} (rs : sReifier a)
  {A} `{!Cofe A} (α : list (IT _ A)) σ :
  (⊢@{iProp Σ} (∃ αv βs σ' k, tp_internal_steps rs α σ (IT_of_V αv :: βs) σ' k))
  → ∃ f : nat → nat,
      ∀ k, uPred_holds
             (∃ αv βs σ', tp_internal_steps (Σ := Σ) rs
                            α σ (IT_of_V αv :: βs) σ' (f k))%I k ε.
Proof.
  set (R := λ k p,
         uPred_holds
           (∃ (αv : ITV (sReifier_ops rs) A) (βs : list (IT (sReifier_ops rs) A))
              (σ' : sReifier_state rs ♯ IT (sReifier_ops rs) A),
              tp_internal_steps (Σ := Σ) rs α σ (IT_of_V αv :: βs) σ' p) k ε).
  intros H.
  apply (AC nat nat R).
  intros x.
  subst R.
  assert (Hemp : uPred_holds (emp : iProp Σ) x ε).
  { uPred.unseal. rewrite /upred.uPred_pure_def //=. }
  pose proof (uPred_in_entails _ _ H x ε (ucmra_unit_validN _) Hemp) as G.
  clear H.
  revert G.
  uPred.unseal.
  intros [αv [βs [σ' [k H]]]].
  exists k, αv, βs, σ'.
  apply H.
Qed.

Definition bounded (f : nat → nat) : Prop :=
  ∃ n, ∀ m, f m ≤ n.

Lemma bounding_fun_bounded_contra (AC : Choice) (XM : Classical) Σ {a} (rs : sReifier a)
  {A} `{!Cofe A} (α : list (IT _ A)) σ (f : nat → nat) (Hf : bounded f → False) :
  (∀ k, uPred_holds
             (∃ αv βs σ', tp_internal_steps (Σ := Σ) rs
                            α σ (IT_of_V αv :: βs) σ' (f k))%I k ε)
  → False.
Proof.
  intros H.
  unfold bounded in Hf.
  pose proof (not_ex_all_not _ _ Hf) as Hf'.
  simpl in Hf'.
  assert (∀ n, ∃ m, f m > n) as Hf''.
  {
    intros n.
    specialize (Hf' n).
    apply not_all_ex_not in Hf'.
    destruct Hf' as [m Hf'].
    exists m.
    lia.
  }
  clear Hf Hf'.
  rename Hf'' into Hf.

Admitted.

Lemma bounding_fun_bounded_reseal Σ {a} (rs : sReifier a)
  {A} `{!Cofe A} (α : list (IT _ A)) σ (f : nat → nat) (Hf : bounded f) :
  (∀ k, uPred_holds
             (∃ αv βs σ', tp_internal_steps (Σ := Σ) rs
                            α σ (IT_of_V αv :: βs) σ' (f k))%I k ε)
  → ∃ k, ⊢@{iProp Σ} (∃ αv βs σ', tp_internal_steps rs α σ (IT_of_V αv :: βs) σ' k).
Proof.
  destruct Hf as [n Hf].
  intros H.
  exists n.
  constructor.
  intros m x _ _; simpl.
  eapply (uPred_mono _ _ m m ε); last lia; last apply ucmra_unit_leastN.
  specialize (H m).
  revert H.
  uPred.unseal.
  intros H.
  destruct H as [αv [βs [σ' H]]].
  exists αv, βs, σ'.
  apply (uPred_in_entails _ _
                 (tp_internal_steps_grow (Σ := Σ) rs
                    α (IT_of_V αv :: βs) σ σ' (f m) n (Hf _)) m
                 ε (ucmra_unit_validN _) H).
Qed.

Lemma extract_steps `{Classical} Σ {a} (rs : sReifier a)
  {A} `{!Cofe A} (α : list (IT _ A)) σ :
  (∃ k, (⊢@{iProp Σ} (∃ αv βs σ', tp_internal_steps rs α σ (IT_of_V αv :: βs) σ' k)))
       → ∃ k αv βs σ', tp_external_steps rs α σ (IT_of_V αv :: βs) σ' k.
Proof.
  intros [k G].
  exists k.
  eapply tp_internal_steps_safe_agnostic; first done.
  apply G.
Qed.

Lemma logrel_adequacy `{Classical} `{Choice} Σ cr n
  (rs : gReifiers NotCtxDep n)
  {A} `{!Cofe A} `{!invGpreS Σ}
  `{!Inhabited (gReifiers_state rs ♯ IT (sReifier_ops (gReifiers_sReifier rs)) A)}
  `{!statePreG rs A Σ} `{!inG Σ (tpoolUR rs A)}
  (α β : IT _ A) σ αv αs σ' (s : stuckness) k :

  let rg := gReifiers_sReifier rs in
  let F := sReifier_ops rg in
  let IT := IT F A in
  let ITV := ITV F A in

  tp_external_steps rg [α] σ (IT_of_V αv :: αs) σ' k →
  (∀ `{H1 : !gitreeGS_gen rs A Σ} `{!tpoolSG rs A Σ} `{HSTATE : !stateG rs A Σ},
     (⊢@{iProp Σ} (£ cr
                   -∗ @has_full_state _ _ rs _ _ _ HSTATE σ
                   -∗ (α) ⪯ₚ (β) @{ rs \ A \ s \ HSTATE })%I)) →
  (∃ k' αv βs st', tp_external_steps (gReifiers_sReifier rs) [β] σ
                     (IT_of_V αv :: βs) st' k').
Proof.
  intros rg ops IT ITV Hsteps Hwp.
  eapply extract_steps.
  pose proof (logrel_adequacy_internal Σ cr n rs α β σ αv αs σ' s k Hsteps Hwp) as J.
  apply internal_steps_bounding_fun_witness in J; last done.
  destruct J as [f J].
  destruct (excluded_middle (bounded f)).
  - apply bounding_fun_bounded_reseal in J.
    + apply J.
    + done.
  - exfalso.
    by eapply bounding_fun_bounded_contra.
Qed.

Section rules.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ} `{!tpoolSG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Lemma IT_Rel_val `{!IntoVal e1 v} `{!IntoVal e2 w}
    : ⊢ (v) ⪯ᵥ (w) @{ rs \ R \ s }
        -∗ (e1) ⪯ₑ (e2) @{ rs \ R \ s }.
  Proof.
    iIntros "H".
    rewrite -(@into_val _ _ _ e1) -(@into_val _ _ _ e2).
    iIntros (j K) "Hpt".
    iApply wp_val.
    iModIntro.
    iExists w.
    iFrame "Hpt H".
  Qed.

  Lemma IT_Rel_Tick_l' e1 e2
    : ⊢ ▷ (£ 1 -∗ (e1) ⪯ₑ (e2) @{ rs \ R \ s })
        -∗ (Tick e1) ⪯ₑ (e2) @{ rs \ R \ s }.
  Proof.
    iIntros "H" (j K) "G".
    iApply wp_tick.
    iNext.
    iIntros "Hlc".
    by iApply ("H" with "Hlc").
  Qed.

  Lemma IT_Rel_Tick_l `{HSTATE : !stateG rs R Σ} e1 e2
    : ⊢ ▷ (£ 1 -∗ (e1) ⪯ₚ (e2) @{ rs \ R \ s \ HSTATE })
        -∗ (Tick e1) ⪯ₚ (e2) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "H HInv".
    iApply IT_Rel_Tick_l'.
    iNext.
    iIntros "Hlc".
    iApply ("H" with "Hlc HInv").
  Qed.

  Lemma IT_Rel_Tick_r
    `{HSTATE : !stateG rs R Σ} e1 e2
    : ⊢ £ 1 -∗ (e1) ⪯ₚ (e2) @{ rs \ R \ s \ HSTATE }
        -∗ e1 ⪯ₚ (Tick e2) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "HCred H #HInv %j %K G".
    iApply fupd_wp; first solve_proper.
    iEval (rewrite hom_tick) in "G".
    iMod (step_tick with "[$HCred $HInv $G]") as "J";
      first set_solver.
    iModIntro.
    iSpecialize ("H" with "HInv").
    iApply ("H" $! j K with "J").
  Qed.

  Lemma IT_Rel_Tick_lr
    `{HSTATE : !stateG rs R Σ} e1 e2
    : ⊢ (e1) ⪯ₚ (e2) @{ rs \ R \ s \ HSTATE }
        -∗ (Tick e1) ⪯ₚ (Tick e2) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "H".
    iApply IT_Rel_Tick_l.
    iNext.
    iIntros "Hlc".
    iApply (IT_Rel_Tick_r with "Hlc H").
  Qed.

  Lemma IT_Rel_bottom_l' e
    : ⊢ (core.Bottom) ⪯ₑ (e) @{ rs \ R \ s }.
  Proof.
    iLöb as "IH".
    iEval (rewrite Bottom_unfold -Tick_eq).
    iApply IT_Rel_Tick_l'.
    iNext.
    by iIntros "_".
  Qed.

  Lemma nfalse_bottom m (α : IT) : ▷^m False ⊢@{iProp} Tick_n m α ≡ core.Bottom.
  Proof.
    induction m as [| m' IH].
    - by iIntros "?".
    - iIntros "H".
      rewrite Bottom_unfold /=.
      rewrite Tick_eq.
      iApply Tau_inj'.
      iNext.
      by iApply IH.
  Qed.

  Lemma IT_Rel_bottom_r `{!SubOfe nat R} `{HSTATE : !stateG rs R Σ}
    : £ 1 ⊢ (Ret 0) ⪯ₚ (core.Bottom) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "HCred HInv".
    iIntros (j K) "Hpt".
    iApply wp_val.
    iAssert (∃ n, ▷^n False)%I as (m) "HF".
    {
      iLöb as "IH".
      iDestruct "IH" as (m) "IH".
      iExists (S m).
      by iNext.
    }
    iRewrite - (nfalse_bottom m (Ret 0) with "HF") in "Hpt".
    iExists (RetV 0).
    iMod (step_steps_not_stateful _ _ _ emp%I _ _ _ (K (Ret 0)) [] m
           with "[$HCred $HInv $Hpt]") as "(_ & J & _)".
    - done.
    - iSplit; first done.
      iIntros (σ).
      iClear "HF".
      iInduction m as [| m' IH].
      + iApply internal_steps_0.
        done.
      + iApply internal_steps_S.
        iExists (K (Tick_n m' (Ret 0))), σ, [], [].
        iSplit; first done.
        iSplit.
        * iLeft.
          iSimpl.
          rewrite hom_tick.
          done.
        * iApply "IH".
    - rewrite IT_of_V_Ret.
      iFrame "J".
      iModIntro.
      rewrite IT_Val_Rel_unfold.
      iLeft.
      iExists ((subOfe_in (inl 0))), ((subOfe_in (inl 0))).
      iSplit.
      + rewrite IT_of_V_Ret.
        by iPureIntro.
      + iSplit.
        * rewrite IT_of_V_Ret.
          by iPureIntro.
        * done.
  Qed.

  Lemma IT_Rel_bottom_l `{HSTATE : !stateG rs R Σ} e
    : ⊢ (core.Bottom) ⪯ₚ (e) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "HInv".
    iApply IT_Rel_bottom_l'.
  Qed.

  Lemma IT_Rel_Vis_l
    `{subR : !subReifier sR rs}
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l e :
    sReifier_re sR op (x, σ) ≡ Some (y, σ', l) →
    k (subEff_outs y) ≡ Next β →
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ'
          -∗ (wptp rs s (listO_map Tau l) (replicate (length (listO_map Tau l)) fork_post))
          ∗ (β) ⪯ₑ (e) @{ rs \ R \ s})
    -∗ (Vis (subEff_opid op) (subEff_ins x) k) ⪯ₑ (e) @{ rs \ R \ s}.
  Proof.
    iIntros (H1 H2) "Hσ G".
    iIntros (j K) "J".
    iApply (wp_subreify_ctx_indep with "Hσ"); [eassumption | eassumption |].
    iNext.
    iIntros "Hlc Hσ".
    iDestruct ("G" with "Hlc Hσ") as "(G1 & G2)".
    iFrame "G1".
    by iApply "G2".
  Qed.

  Lemma IT_Rel_Vis_r
    `(HSTATE : !stateG rs R Σ)
    `{subR : !subReifier sR rs}
    e
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l
    : £ 1
      -∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
      -∗ k (subEff_outs y) ≡ Next β
      -∗ ▷ has_substate σ
      -∗ (([∗ list] i ∈ listO_map Tau l, ∃ j0 : natO, j0 ⤇ i)
          -∗ has_substate σ'
          -∗ (e) ⪯ₚ (β) @{ rs \ R \ s \ HSTATE })
      -∗ (e) ⪯ₚ (Vis (subEff_opid op) (subEff_ins x) k) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "HCred Heq1 Heq2 Hst H #HInv %j %K G".
    iApply fupd_wp; first solve_proper.
    iMod (step_reify_hom with "[$HCred $Heq1 $Heq2 $Hst $HInv $G]")
      as "(J1 & J2 & J3)";
      first set_solver.
    iModIntro.
    iApply ("H" with "J2 J3 HInv J1").
  Qed.

End rules.

Require Import gitrees.gitree.subofe.
Require Import gitrees.gitree.lambda.
Require Import gitrees.effects.store.
Require Import gitrees.lib.factorial.

Section example.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context `{!subReifier reify_store rs}.
  Context (R : ofe) `{!Cofe R}.
  Context `{!SubOfe natO R, !SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ}.
  Context `{!tpoolSG rs R Σ} `{!heapG rs R Σ}.
  Context `{HSTATE : !stateG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Example prog3 : ITV := FunV (Next (λne x, x)).

  Program Example prog4 : IT := λit x, LET (Ret 5) (constO x).
  Next Obligation.
    intros ??? G.
    by do 2 f_equiv.
  Qed.

  Program Example prog5 : IT := λit x, ALLOC (Ret 5) (constO x).
  Next Obligation.
    intros ??? H.
    by do 2 f_equiv.
  Qed.

  Program Example prog6 : IT := (IT_of_V prog3) ⊙ (IT_of_V prog3).

  (* do reverse *)
  Example prog3_prog4_rel
    : ⊢ (IT_of_V prog3) ⪯ₚ (prog4) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "#HInv".
    iApply IT_Rel_val.
    rewrite IT_Val_Rel_unfold.
    iRight.
    iExists (Next (λne x, x)), _.
    iSplit; first done.
    iSplit; first done.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "H".
    iEval (rewrite !APP'_Fun_l /= -!Tick_eq LET_Val /=).
    iApply (IT_Rel_Tick_lr with "[H] HInv").
    iIntros "_".
    iApply IT_Rel_val.
    iApply "H".
  Qed.

  Example prog4_prog3_rel
    : ⊢ (prog4) ⪯ₚ (IT_of_V prog3) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "#HInv".
    iApply IT_Rel_val.
    rewrite IT_Val_Rel_unfold.
    iRight.
    iExists _, _.
    iSplit; first done.
    iSplit; first done.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "H".
    iEval (rewrite !APP'_Fun_l /= -!Tick_eq LET_Val /=).
    iApply (IT_Rel_Tick_lr with "[H] HInv").
    iIntros "_".
    iApply IT_Rel_val.
    iApply "H".
  Qed.

  Example prog5_prog3_rel
    : heap_ctx rs
      -∗ (prog5) ⪯ₚ (IT_of_V prog3) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "#HHeap #HInv".
    iApply IT_Rel_val.
    rewrite IT_Val_Rel_unfold.
    iRight.
    iExists _, (Next (λne x, x)).
    iSplit; first done.
    iSplit; first done.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "#H".
    iEval (rewrite !APP'_Fun_l /= -!Tick_eq).
    iApply (IT_Rel_Tick_l with "[H] HInv").
    iNext.
    iIntros "Hlc _ %j %K Hpt".
    iApply (wp_alloc with "HHeap"); first solve_proper.
    do 2 iNext.
    iIntros (l) "Hpt'"; iSimpl.
    iApply wp_val.
    iMod (step_steps_not_stateful _ _ _ emp%I _ _ _ (K (IT_of_V w)) [] 1
           with "[$Hlc $HInv $Hpt]") as "(_ & J & _)";
      first set_solver.
    {
      iSplit; first done.
      iIntros (σ).
      iApply internal_steps_S.
      iExists _, _, [], [].
      iSplit; [done | iSplit]; last (iApply internal_steps_0; by iSplit).
      iLeft.
      rewrite hom_tick.
      by iSplit.
    }
    iModIntro.
    iExists w.
    by iFrame "H J".
  Qed.

  Program Definition heap_ctx_rel :=
    inv stateN
      (∃ σ rest, @has_full_state _ _ rs _ _ _ HSTATE
                   (gState_recomp rest (sR_state σ))
            ∗ own (heapG_name rs) (●V (fmap (M := gmap locO) to_agree σ)))%I.

  Example prog5_prog5_rel
    `{!Inhabited (gState_rest sR_idx rs ♯
                    ITF_solution.IT (sReifier_ops (gReifiers_sReifier rs)) R)}
    : heap_ctx rs -∗ heap_ctx_rel
      -∗ (prog5) ⪯ₚ (prog5) @{ rs \ R \ s \ HSTATE }.
  Proof.
    iIntros "#HHeap #HHeap' #HInv".
    iApply IT_Rel_val.
    rewrite IT_Val_Rel_unfold.
    iRight.
    iExists _, _.
    iSplit; first done.
    iSplit; first done.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "#H".
    iEval (rewrite !APP'_Fun_l /= -!Tick_eq).
    iApply (IT_Rel_Tick_l with "[H] HInv").
    iNext. iIntros "Hlc".
    iIntros "_ %j %K Hpt".

    iApply (wp_alloc with "HHeap"); first solve_proper.
    do 2 iNext.
    iIntros (l) "Hpt'".
    iSimpl.
    iApply wp_val.
    iExists w.
    iFrame "H".

    iInv "HHeap'" as "(%σ & %rest & Hstate & Hheap)" "Hcl".
    set (l' := (Loc.fresh (dom σ))).
    iMod (step_steps with "[$Hheap $Hlc $HInv $Hstate $Hpt]")
      as "(J1 & J2 & J3 & J4)".
    {
      rewrite /specN /stateN.
      apply namespaces.coPset_subseteq_difference_r; last done.
      apply ndot_ne_disjoint.
      done.
    }
    {
      iApply internal_steps_S.
      iExists _, (gState_recomp rest (sR_state σ)), [], []. iSplit; first done.
      iSplit.
      { iApply internal_step_hom. iLeft. iSplit; done. }
      iApply internal_steps_S.

      iExists (K (IT_of_V w)),
        (gState_recomp rest (sR_state (<[l' := Next (Ret 5)]>σ))),
        [], []. iSplit; first done.
      iSplit.
      {
        iApply internal_step_hom. iRight. iExists _, _, _. iSplit; first done.
        iEval (rewrite Tick_eq).
        simplify_eq; cbn-[gState_recomp].
        rewrite (reify_vis_eq_ctx_indep _ _ _ _ _ _ _ []) //; first last.
        {
          eapply (@subReifier_reify _ NotCtxDep reify_store rs _ IT _
                    (inr (inr (inl ())))
                    (1, Next (Ret 5)) _ σ
                    (<[l':=Next (Ret 5)]> σ) rest []).
          simpl.
          rewrite Loc.add_0.
          subst l'.
          rewrite insert_empty -insert_union_singleton_l.
          reflexivity.
        }
      }
      iApply internal_steps_0.
      iSplit; done.
    }
    iMod (istate_alloc _ (Ret 5) l' with "J1") as "(T1 & T2)".
    {
      apply (not_elem_of_dom_1 (M:=gmap loc)).
      subst l'.
      rewrite dom_fmap_L.
      rewrite -(Loc.add_0 (Loc.fresh (dom σ))).
      apply Loc.fresh_fresh. lia.
    }
    iClear "J3".
    iFrame "J2".

    iApply ("Hcl" with "[J4 T1]").
    iNext.
    iExists _, _; iFrame "J4".
    rewrite -(fmap_insert to_agree σ).
    iFrame "T1".
  Qed.

End example.

(* Inductive class : (IT -> IT) -> Prop := *)
(* | id : class idfun *)
(* | comp f g : class f -> class g -> class (compose f g) *)
(* | tricky (C' : IT -> IT -n> IT) : (∀ x, class (C' x)) -> class (λ x, Fun (Next (C' x))). *)
