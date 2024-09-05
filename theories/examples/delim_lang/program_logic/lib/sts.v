From iris.algebra Require Import auth gmap.
From iris.base_logic Require Import invariants.
From iris.algebra Require Import mra.
From iris.proofmode Require Import proofmode.
From WBLogic.program_logic Require Import ghost_stacks weakestpre.

Record STS := {
  STS_state :> Type;
  state_inh :: Inhabited STS_state;
  pub_rel : STS_state → STS_state → Prop;
  pri_rel : STS_state → STS_state → Prop;
  pub_rel_po :: PreOrder pub_rel;
  pri_rel_po :: PreOrder pri_rel;
  pub_pri_incl : ∀ s s', pub_rel s s' → pri_rel s s'
}.

Definition STSUR (S : STS) := authUR (mraUR (pub_rel S)).

Definition STSΣ S : gFunctors := #[GFunctor (STSUR S)].

Global Instance subG_STSΣ_ing S Σ : subG (STSΣ S) Σ → inG Σ (STSUR S).
Proof. solve_inG. Qed.

Section STS.
  Context {S} `{!irisGS Λ Σ, !inG Σ (STSUR S), !gstacksIG Σ}.

  Definition sts_config : Type := gstack * S.

  Definition state_of (sc : sts_config) : S := sc.2.

  Definition related_public (sc sc' : sts_config) : iProp Σ :=
    ⌜sc.1 = sc'.1⌝ ∗ ⌜pub_rel S (state_of sc) (state_of sc')⌝.

  Definition related_private (sc sc' : sts_config) : iProp Σ :=
    ∃ γ γ', ⌜sc'.1 = gpush γ' sc.1⌝ ∗ ⌜gtop sc.1 = Some γ⌝ ∗
      own γ (● (to_mra (state_of sc))) ∗ ⌜pri_rel S (state_of sc) (state_of sc')⌝.

  Definition STS_inv_name (N : ghost_id) := nroot.@"gstack".@N.

  Definition sts_config_frag N (sc : sts_config) : iProp Σ :=
    ∃ γ, gstack_full N sc.1 ∗ ⌜gtop sc.1 = Some γ⌝ ∗ own γ (◯ (to_mra sc.2)).

  Definition sts_config_full N (sc : sts_config) : iProp Σ :=
    (∃ γ, gstack_frag N sc.1 ∗ ⌜gtop sc.1 = Some γ⌝ ∗ own γ (● (to_mra sc.2))).

  Definition STS_inv (N : ghost_id) (P : S → iProp Σ) : iProp Σ :=
    inv (STS_inv_name N) (∃ sc, sts_config_full N sc ∗ P (state_of sc)).

  Lemma sts_configs_update_frag N sc sc' :
    sts_config_full N sc ⊢ sts_config_frag N sc' ==∗ sts_config_full N sc ∗ sts_config_frag N sc.
  Proof.
    iDestruct 1 as (?) "(Hstfr & % & Hprfl)".
    iDestruct 1 as (?) "(Hstfl & % & Hprfr)".
    iDestruct (gstacks_agree with "Hstfl Hstfr") as %?.
    destruct sc; destruct sc'; simplify_eq/=.
    iDestruct (own_valid_2 with "Hprfl Hprfr") as %[Hincl ?]%auth_both_valid_discrete.
    rewrite to_mra_included in Hincl.
    iClear "Hprfr".
    iMod (own_update with "Hprfl") as "[Hprfl Hprfr]".
    { apply auth_update_alloc; apply mra_local_update_grow; reflexivity. }
    iModIntro.
    iSplitL "Hstfr Hprfl"; iFrame; iExists _; iFrame; done.
  Qed.

  Lemma sts_configs_pub_related N sc sc' :
    sts_config_full N sc ⊢ sts_config_frag N sc' -∗ related_public sc' sc.
  Proof.
    iDestruct 1 as (?) "(Hstfr & % & Hprfl)".
    iDestruct 1 as (?) "(Hstfl & % & Hprfr)".
    iDestruct (gstacks_agree with "Hstfl Hstfr") as %?.
    destruct sc; destruct sc'; simplify_eq/=.
    iDestruct (own_valid_2 with "Hprfl Hprfr") as %[Hincl ?]%auth_both_valid_discrete.
    rewrite to_mra_included in Hincl; done.
  Qed.

  Lemma related_private_public sc sc' sc'' :
    related_private sc sc' ⊢ related_public sc' sc'' -∗ related_private sc sc''.
  Proof.
    destruct sc as [? ?]; destruct sc' as [? ?]; destruct sc'' as [? ?].
    iDestruct 1 as (? ?) "(%&%& HPrfl &%)".
    iIntros "[% %]".
    simplify_eq/=.
    iExists _, _; iFrame; simpl.
    iSplit; first done.
    iSplit; first done.
    iPureIntro.
    etrans; first eassumption.
    by apply pub_pri_incl.
  Qed.

  Lemma related_public_trans sc sc' sc'' :
    related_public sc sc' ⊢ related_public sc' sc'' -∗ related_public sc sc''.
  Proof.
    destruct sc as [? ?]; destruct sc' as [? ?]; destruct sc'' as [? ?].
    iIntros "[% %] [% %]"; simplify_eq/=; iSplit; iPureIntro; first done.
    etrans; eassumption.
  Qed.

  Lemma related_public_states sc sc' :
    related_public sc sc' ⊢ ⌜pub_rel S (state_of sc) (state_of sc')⌝.
  Proof. iIntros "[% %]"; done. Qed.

  Lemma sts_make_public_trans N sc s' :
    pub_rel S (state_of sc) s' →
    sts_config_frag N sc ⊢ sts_config_full N sc ==∗
      ∃ sc', related_public sc sc' ∗ ⌜state_of sc' = s'⌝ ∗ sts_config_frag N sc' ∗ sts_config_full N sc'.
  Proof.
    destruct sc as [? s].
    iIntros (?).
    iDestruct 1 as (γ) "(Hfl & % & _)".
    iDestruct 1 as (γ') "(Hfr & % & HPrfl)".
    simplify_eq/=.
    iMod (own_update with "HPrfl") as "[HPrfl HPrfr]".
    { apply auth_update_alloc; apply mra_local_update_grow; eassumption. }
    iModIntro; iExists (_, s').
    iSplit; first done. iSplit; first done.
    iSplitL "Hfl HPrfr"; iExists _; iFrame; done.
  Qed.

  Lemma sts_make_private_trans N sc s' :
    pri_rel S (state_of sc) s' →
    sts_config_frag N sc ⊢ sts_config_full N sc ==∗
      ∃ sc', related_private sc sc' ∗ ⌜state_of sc' = s'⌝ ∗ sts_config_frag N sc' ∗ sts_config_full N sc'.
  Proof.
    destruct sc as [? s].
    iIntros (?).
    iDestruct 1 as (γ) "(Hfl & Htop & _)".
    iDestruct "Htop" as %[? ?]%gtop_inv.
    iDestruct 1 as (γ') "(Hfr & % & HPrfl)".
    simplify_eq/=.
    iMod (own_alloc (● (to_mra s') ⋅ ◯ (to_mra s'))) as (γ'') "[HPrfl' HPrfr]";
      first by apply auth_both_valid.
    iMod (gstack_push _ _ _ γ'' with "Hfl Hfr") as "[Hfl Hfr]".
    iModIntro; iExists (_, s').
    iSplitL "HPrfl".
    { iExists _, _; iFrame; eauto. }
    iSplit; first done.
    iSplitL "Hfl HPrfr"; iExists _; iFrame; done.
  Qed.

  Lemma sts_make_undo_private_trans N sc sc' :
    related_private sc sc' ⊢
    sts_config_frag N sc' -∗ sts_config_full N sc' ==∗ sts_config_frag N sc ∗ sts_config_full N sc.
  Proof.
    destruct sc as [? s]; destruct sc' as [? s'].
    iDestruct 1 as (? ?) "(% & % & HPrfl & %)".
    simplify_eq/=.
    iDestruct 1 as (γ1) "(Hfl & Htop & _)".
    iDestruct "Htop" as %[? ?]%gtop_inv.
    iDestruct 1 as (γ2) "(Hfr & % & _)".
    simplify_eq/=.
    iMod (gstack_pop with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (own_update with "HPrfl") as "[HPrfl HPrfr]".
    { apply auth_update_alloc; apply mra_local_update_grow; reflexivity. }
    iModIntro.
    iSplitL "HPrfr Hfl".
    { iExists _; iFrame; eauto. }
    iExists _; iFrame; done.
  Qed.

  Lemma make_STS {E N} (s : S) (P : S → iProp Σ) :
    P s ⊢ gstack_full N [] -∗ gstack_frag N [] -∗ |={E}=> STS_inv N P ∗ ∃ stk, gstack_full N stk.
  Proof.
    iIntros "HP Hfl Hfr".
    iMod (own_alloc (● (to_mra s))) as (γ) "Hs"; first by apply auth_auth_valid.
    iMod (gstack_push _ _ _ γ with "Hfl Hfr") as "[Hfl Hfr]".
    iMod (inv_alloc (STS_inv_name N) _
      (∃ sc, sts_config_full N sc ∗ P sc.2)%I with "[- Hfl]")
    as "#Hinv".
    { iNext. iExists (_, _); iFrame "HP Hfr". iExists _; iFrame; done. }
    iModIntro; iFrame "#".
    iExists _; iFrame.
  Qed.

  Lemma wbwp_sts_get_state E N P out e Φ :
    ↑(STS_inv_name N) ⊆ E →
    N ∉ out →
    STS_inv N P -∗
    (∀ sc, sts_config_frag N sc -∗
      WBWP e @ (out ∪ {[N]}); E {{v, Φ v ∗ ∃ sc', sts_config_frag N sc' ∗ related_public sc sc' }}) -∗
    WBWP e @ out; E {{ Φ }}.
  Proof.
    iIntros (? ?) "#Hinv HWBWP".
    iAssert (|={E}=> gstack_exists N)%I as ">#Hex".
    { iInv (STS_inv_name N) as (?) "[>Hfl ?]". iDestruct "Hfl" as (?) "(? & ?)".
      iDestruct (gstack_frag_exists with "[$]") as "#?".
      iModIntro. iSplitL; last done. iNext. iExists _; iFrame. iExists _; iFrame. }
    iApply (wbwp_get_gstack_full with "[$] [HWBWP]"); first done.
    iIntros (stk) "Hfl".
    iApply fupd_wbwp.
    iInv (STS_inv_name N) as (?) "(>Hscfl & Hrest)" "Hcl".
    iDestruct "Hscfl" as (?) "(Hfr & % & Hstsfl)".
    iDestruct (gstacks_agree with "Hfl Hfr") as %?; subst.
    iMod (own_update with "Hstsfl") as "[Hstsfl Hstsfr]".
    { apply auth_update_alloc; apply mra_local_update_grow; reflexivity. }
    iMod ("Hcl" with "[Hfr Hrest Hstsfl]") as "_".
    { iNext; iExists _; iFrame; iExists _; iFrame; done. }
    iModIntro.
    iApply (wbwp_wand with "[-]").
    { iApply ("HWBWP" $! (_, _)). iExists _; iFrame; done. }
    simpl.
    iIntros (w) "[$ Hsc']".
    iDestruct "Hsc'" as ([]) "[Hsc' [% %]]"; simplify_eq/=.
    iDestruct "Hsc'" as (?) "[$ ?]".
  Qed.

  Lemma wbwp_sts_mend N sc E out e Φ :
    sts_config_frag N sc -∗
    WBWP e @ out ∖ {[N]}; E {{ Φ }} -∗
    WBWP e @ out; E {{v, sts_config_frag N sc ∗ Φ v }}.
  Proof.
    iIntros "Hfl HWBWP".
    iDestruct "Hfl" as (γ) "(Hfl&%&?)".
    iApply (wbwp_wand with "[Hfl HWBWP]").
    { iApply (wbwp_mend with "Hfl HWBWP"). }
    iIntros (v) "[? $]"; iExists _; iFrame; done.
  Qed.

End STS.

Global Arguments sts_config _ : clear implicits.
