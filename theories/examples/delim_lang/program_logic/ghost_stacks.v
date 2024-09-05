From iris.algebra Require Import auth gmap gset excl frac.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.

Definition ghost_id := gname.

Definition gstack := list gname.
Definition gstackO := listO gnameO.

Definition gsingleton (γ : gname) : gstack := [γ].
Definition gpush (γ : gname) (s : gstack) : gstack := γ :: s.
Definition gpop (s : gstack) : gstack := tail s.
Definition gtop (s : gstack) : option gname := head s.

Lemma gtop_gpush γ s : gtop (gpush γ s) = Some γ.
Proof. done. Qed.
Lemma gtop_gsingleton γ : gtop (gsingleton γ) = Some γ.
Proof. done. Qed.
Lemma gpop_gpush γ s : gpop (gpush γ s) = s.
Proof. done. Qed.
Lemma gtop_inv γ s : gtop s = Some γ → ∃ s', s = gpush γ s'.
Proof. destruct s; first done; eexists; simplify_eq/=; reflexivity. Qed.

Definition gstackUR := optionUR (exclR gstackO).

Definition gstacks := gmap ghost_id gstack.

Definition gstacksΣ := #[GFunctor (authUR (gsetUR ghost_id)); GFunctor (authUR gstackUR)].

Class gstacksGpre Σ := {
    gstacksGpre_dom_ing :: inG Σ (authUR (gsetUR ghost_id));
    gstacksGpre_ing :: inG Σ (authUR gstackUR);
  }.

Class gstacksIG Σ := {
    gstacks_dom_ing :: inG Σ (authUR (gsetUR ghost_id));
    gstacks_ing :: inG Σ (authUR gstackUR);
    gstacks_name : gname;
  }.

Global Instance gstacks_subΣ_inG Σ : subG gstacksΣ Σ → gstacksGpre Σ.
Proof. solve_inG. Qed.

Section ghost_stacks.
  Context `{!gstacksIG Σ}.

  Definition gstack_frag (n : ghost_id) (s : gstack) : iProp Σ :=
    own gstacks_name (◯ {[n]}) ∗ own n (◯ Excl' s).
  Definition gstack_full (n : ghost_id) (s : gstack) : iProp Σ :=
    own gstacks_name (◯ {[n]}) ∗ own n (● Excl' s).

  Definition gstack_exists (n : ghost_id) : iProp Σ := own gstacks_name (◯ {[n]}).

  Definition gstacks_except (M : gstacks) (N : gset ghost_id) : iProp Σ :=
    ⌜N ⊆ dom M⌝ ∗ own gstacks_name (● dom M) ∗
    [∗ map] n ↦ s ∈ M, if bool_decide (n ∈ N) then True else gstack_full n s.

  Global Typeclasses Opaque gstack_frag gstack_full gstacks_except gstack_exists.

  Global Instance gstack_frag_Timeless n s : Timeless (gstack_frag n s).
  Proof. rewrite /gstack_frag; apply _. Qed.
  Global Instance gstack_full_Timeless n s : Timeless (gstack_full n s).
  Proof. rewrite /gstack_full; apply _. Qed.
  Global Instance gstack_exists_Timeless n : Timeless (gstack_exists n).
  Proof. rewrite /gstack_exists; apply _. Qed.

  Global Instance gstack_exists_Persistent n : Persistent (gstack_exists n).
  Proof. rewrite /gstack_exists; apply _. Qed.

  Global Instance gstacks_except_Timeless M N : Timeless (gstacks_except M N).
  Proof.
    apply bi.sep_timeless; first apply _.
    apply bi.sep_timeless; first apply _.
    apply big_sepM_timeless; intros; destruct bool_decide; apply _.
  Qed.

  Lemma gstacks_agree n s s' : gstack_full n s -∗ gstack_frag n s' -∗ ⌜s = s'⌝.
  Proof.
    rewrite /gstack_frag /gstack_full.
    iIntros "[_ H1] [_ H2]".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl _]%auth_both_valid_discrete; iPureIntro.
    apply Excl_included, leibniz_equiv in Hvl; done.
  Qed.

  Lemma gstack_frag_unique n s s' : gstack_frag n s -∗ gstack_frag n s' -∗ False.
  Proof.
    rewrite /gstack_frag.
    iIntros "[_ H1] [_ H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvl.
    rewrite -auth_frag_op in Hvl.
    apply auth_frag_valid_1 in Hvl; done.
  Qed.

  Lemma gstack_full_unique n s s' : gstack_full n s -∗ gstack_full n s' -∗ False.
  Proof.
    rewrite /gstack_full.
    iIntros "[_ H1] [_ H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvl.
    rewrite auth_auth_op_valid in Hvl; done.
  Qed.

  Lemma gstack_push n s s' γ :
    gstack_full n s -∗ gstack_frag n s' ==∗ gstack_full n (gpush γ s) ∗ gstack_frag n (gpush γ s').
  Proof.
    iIntros "Hfl Hfr".
    iDestruct (gstacks_agree with "Hfl Hfr") as %<-.
    rewrite /gstack_frag /gstack_full.
    iDestruct "Hfl" as "[$ Hfl]".
    iDestruct "Hfr" as "[$ Hfr]".
    iMod (own_update_2 _ _ _ (● _ ⋅ ◯ _) with "Hfl Hfr") as "[$ $]"; last done.
    apply auth_update, option_local_update, exclusive_local_update; done.
  Qed.

  Lemma gstack_pop n s s' γ γ' :
    gstack_full n (gpush γ s) -∗ gstack_frag n (gpush γ' s') ==∗ gstack_full n s ∗ gstack_frag n s'.
  Proof.
    iIntros "Hfl Hfr".
    iDestruct (gstacks_agree with "Hfl Hfr") as %?; simplify_eq.
    rewrite /gstack_frag /gstack_full.
    iDestruct "Hfl" as "[$ Hfl]".
    iDestruct "Hfr" as "[$ Hfr]".
    iMod (own_update_2 _ _ _ (● _ ⋅ ◯ _) with "Hfl Hfr") as "[$ $]"; last done.
    apply auth_update, option_local_update, exclusive_local_update; done.
  Qed.

  Lemma gstack_frag_exists n s : gstack_frag n s -∗ gstack_exists n.
  Proof. rewrite /gstack_frag /gstack_exists; iIntros "[$ ?]". Qed.

  Lemma gstack_full_exists n s : gstack_full n s -∗ gstack_exists n.
  Proof. rewrite /gstack_full /gstack_exists; iIntros "[$ ?]". Qed.

  Lemma gstack_exists_in M N n : gstack_exists n -∗ gstacks_except M N -∗ ⌜n ∈ dom M⌝.
  Proof.
    rewrite /gstack_exists /gstacks_except.
    iIntros "H1 (_&H2&_)".
    iDestruct (own_valid_2 with "H2 H1") as %[?%gset_included ?]%auth_both_valid_discrete.
    iPureIntro.
    set_solver.
  Qed.

  Lemma gstack_frag_in M N n s : gstack_frag n s -∗ gstacks_except M N -∗ ⌜n ∈ dom M⌝.
  Proof.
    iIntros "Hfr Hgs".
    iDestruct (gstack_frag_exists with "Hfr") as "#?".
    iApply gstack_exists_in; done.
  Qed.

  Lemma gstack_frag_not_out_agree M N n s :
    n ∉ N → gstack_frag n s -∗ gstacks_except M N -∗ ⌜M !! n = Some s⌝.
  Proof.
    iIntros (?) "Hfr Hgs".
    iDestruct (gstack_frag_in with "Hfr Hgs") as %[s' Hs']%elem_of_dom.
    rewrite /gstack_frag /gstacks_except.
    iDestruct "Hgs" as "[% [? Hfls]]".
    iDestruct (big_sepM_lookup _ _ n with "Hfls") as "Hfl"; first eassumption.
    rewrite bool_decide_eq_false_2; last done.
    iDestruct (gstacks_agree with "Hfl Hfr") as %->; done.
  Qed.

  Lemma gstack_full_in M N n s : gstack_full n s -∗ gstacks_except M N -∗ ⌜n ∈ dom M⌝.
  Proof.
    iIntros "Hfr Hgs".
    iDestruct (gstack_full_exists with "Hfr") as "#?".
    iApply gstack_exists_in; done.
  Qed.

  Lemma gstack_full_is_out M N n s : gstack_full n s -∗ gstacks_except M N -∗ ⌜n ∈ N⌝.
  Proof.
    destruct (decide (n ∈ N)); first by auto.
    iIntros "Hfl Hgs".
    iDestruct (gstack_full_in with "Hfl Hgs") as %[s' Hs']%elem_of_dom.
    rewrite /gstacks_except.
    iDestruct "Hgs" as "[% [? Hfls]]".
    iDestruct (big_sepM_lookup _ _ n with "Hfls") as "Hfl'"; first eassumption.
    rewrite bool_decide_eq_false_2; last done.
    iDestruct (gstack_full_unique with "Hfl Hfl'") as "?"; done.
  Qed.

  Lemma gstacks_take_out M N n :
    n ∉ N →
    gstack_exists n -∗
    gstacks_except M N -∗ ∃ s, ⌜M !! n = Some s⌝ ∗ gstacks_except M (N ∪ {[n]}) ∗ gstack_full n s.
  Proof.
    iIntros (Hn) "#Hex Hgs".
    iDestruct (gstack_exists_in with "Hex Hgs") as %?.
    destruct (M !! n) as [s|] eqn:HMn; last first.
    { apply not_elem_of_dom in HMn; set_solver. }
    iExists s; iSplit; first done.
    rewrite /gstacks_except.
    iDestruct "Hgs" as "(%&$&Hgs)".
    replace M with (delete n M ∪ {[n := s]}); last first.
    { apply map_eq; intros i; destruct (decide (i = n)) as [->|].
      - rewrite lookup_union lookup_singleton lookup_delete //.
      - rewrite lookup_union lookup_singleton_ne // lookup_delete_ne //.
        case: (M !! i); done. }
    assert (delete n M ##ₘ {[n := s]}).
    { apply map_disjoint_spec; intros i ? ? Hdl [-> ->]%lookup_singleton_Some.
      rewrite lookup_delete in Hdl; done. }
    repeat (rewrite big_sepM_union; last done).
    rewrite !big_sepM_singleton.
    rewrite bool_decide_eq_false_2; last set_solver.
    rewrite bool_decide_eq_true_2; last set_solver.
    iDestruct "Hgs" as "[Hgs $]".
    iSplit; first by iPureIntro; set_solver.
    iSplit; last done.
    iApply big_sepM_mono; last iAssumption.
    intros i ? ?; simpl.
    destruct (decide (i = n)) as [->|].
    { rewrite [bool_decide (n ∈ N ∪ _)]bool_decide_eq_true_2; [auto|set_solver]. }
    destruct (decide (i ∈ N)).
    { repeat (rewrite bool_decide_eq_true_2; last set_solver); done. }
    { repeat (rewrite bool_decide_eq_false_2; last set_solver); done. }
  Qed.

  Lemma gstacks_put_back M N n s :
    M !! n = Some s →
    gstack_full n s -∗ gstacks_except M N -∗ gstacks_except M (N ∖ {[n]}).
  Proof.
    iIntros (HMns) "Hfl Hgs".
    iDestruct (gstack_full_is_out with "Hfl Hgs") as %?.
    rewrite /gstacks_except.
    iDestruct "Hgs" as "[% [$ Hgs]]".
    iSplit; first by iPureIntro; set_solver.
    replace M with (delete n M ∪ {[n := s]}); last first.
    { apply map_eq; intros i; destruct (decide (i = n)) as [->|].
      - rewrite lookup_union lookup_singleton lookup_delete //.
      - rewrite lookup_union lookup_singleton_ne // lookup_delete_ne //.
        case: (M !! i); done. }
    assert (delete n M ##ₘ {[n := s]}).
    { apply map_disjoint_spec; intros i ? ? Hdl [-> ->]%lookup_singleton_Some.
      rewrite lookup_delete in Hdl; done. }
    repeat (rewrite big_sepM_union; last done).
    iDestruct "Hgs" as "[Hgs _]".
    rewrite !big_sepM_singleton.
    rewrite bool_decide_eq_false_2; last set_solver.
    iFrame "Hfl".
    iApply big_sepM_mono; last iAssumption.
    intros i ? Hnmi; simpl.
    assert (i ≠ n).
    { intros ->; rewrite lookup_delete in Hnmi; done. }
    destruct (decide (i ∈ N)).
    { repeat (rewrite bool_decide_eq_true_2; last set_solver); done. }
    { repeat (rewrite bool_decide_eq_false_2; last set_solver); done. }
  Qed.

  Lemma gstacks_out_swap M N n s :
    n ∈ N → gstacks_except M N -∗ gstacks_except (<[n := s]>M) N.
  Proof.
    rewrite /gstacks_except.
    iIntros (HnN) "HM".
    iDestruct "HM" as "[% HM]".
    assert (dom (<[n := s]> M) = dom M) as Hdomeq by set_solver.
    rewrite Hdomeq.
    iSplit; first done.
    iDestruct "HM" as "[$ HM]".
    destruct (M !! n) as [s'|] eqn:Heq; last first.
    { apply not_elem_of_dom in Heq; set_solver. }
    replace M with (delete n M ∪ {[n := s']}); last first.
    { apply map_eq; intros i; destruct (decide (i = n)) as [->|].
      - rewrite lookup_union lookup_singleton lookup_delete //.
      - rewrite lookup_union lookup_singleton_ne // lookup_delete_ne //.
        case: (M !! i); done. }
    assert (delete n M ##ₘ {[n := s']}).
    { apply map_disjoint_spec; intros i ? ? Hdl [-> ->]%lookup_singleton_Some.
      rewrite lookup_delete in Hdl; done. }
    replace (<[n:=s]> (delete n M ∪ {[n := s']})) with (delete n M ∪ {[n := s]}); last first.
    { apply map_eq; intros i. destruct (decide (i = n)) as [->|].
      - rewrite lookup_insert lookup_union lookup_delete lookup_singleton //.
      - rewrite lookup_insert_ne // !lookup_union !lookup_singleton_ne //. }
    assert (delete n M ##ₘ {[n := s]}).
    { apply map_disjoint_spec; intros i ? ? Hdl [-> ->]%lookup_singleton_Some.
      rewrite lookup_delete in Hdl; done. }
    repeat (rewrite big_sepM_union; last done).
    iDestruct "HM" as "[HM _]".
    rewrite !big_sepM_singleton.
    rewrite bool_decide_eq_true_2; last done.
    iSplit; last done.
    iApply big_sepM_mono; last iAssumption.
    intros i ? Hnmi; simpl.
    assert (i ≠ n).
    { intros ->; rewrite lookup_delete in Hnmi; done. }
    destruct (decide (i ∈ N)).
    { repeat (rewrite bool_decide_eq_true_2; last set_solver); done. }
    { repeat (rewrite bool_decide_eq_false_2; last set_solver); done. }
  Qed.

  Lemma gstacks_except_included M N : gstacks_except M N -∗ ⌜N ⊆ dom M⌝.
  Proof. rewrite /gstacks_except; iIntros "[% ?]"; done. Qed.

  Lemma gstack_alloc M N :
    gstacks_except M N ==∗ ∃ n, ⌜n ∉ dom M⌝ ∗ gstacks_except (<[n := []]>M) N ∗ gstack_frag n [].
  Proof.
    rewrite /gstacks_except /gstack_full /gstack_frag.
    iIntros "(%&Hdm&HM)".
    iMod (own_alloc_cofinite (● Excl' [] ⋅ ◯ Excl' []) (dom M)) as (n) "[%HnM [Hfl Hfr]]".
    { apply auth_both_valid_2; done. }
    iMod (own_update _ _ (● ({[n]} ∪ dom M) ⋅ ◯ ({[n]} ∪ dom M)) with "Hdm") as "[Hdm Hn]".
    { apply auth_update_alloc; apply gset_local_update; set_solver. }
    iAssert (own gstacks_name (◯ {[n]})) as "#?".
    { rewrite -gset_op; iDestruct "Hn" as "[$ _]". }
    iModIntro.
    iExists n.
    iSplit; first done.
    iFrame "#".
    rewrite dom_insert.
    iFrame "Hfr Hdm".
    iSplit; first by iPureIntro; set_solver.
    rewrite big_sepM_insert; last by apply not_elem_of_dom.
    rewrite bool_decide_eq_false_2; last set_solver.
    iFrame "#"; iFrame.
  Qed.

End ghost_stacks.

Lemma gstacks_init `{!gstacksGpre Σ} : ⊢ |==> ∃ _ : gstacksIG Σ, gstacks_except ∅ ∅.
Proof.
  rewrite /gstacks_except.
  iIntros "".
  iMod (own_alloc (● ∅)) as (γ) "Hdm"; first by apply auth_auth_valid.
  iModIntro.
  iExists {| gstacks_name := γ |}.
  iSplit; first done.
  rewrite dom_empty big_sepM_empty; auto.
Qed.
