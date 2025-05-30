(* This file is copied and adapted from the weakestpre file in the iris development. *)

From stdpp Require Export coPset.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From gitrees Require Export prelude gitree lang_generic hom.
Require Export gitrees.gitree.weakestpre.
From gitrees Require Export utils.ghost_stacks utils.clwp.
Import uPred.

Section wbwp.
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
  Notation istep := (internal_step rG).
  Notation isteps := (internal_steps rG).
  Notation sstep := (external_step rG).
  Notation ssteps := (external_steps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!gitreeGS_gen rs A Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Program Definition wbwp `{!gstacksIG Σ}
    (E : coPset) (out : gset ghost_id)
    (e : IT) (Φ : ITV -n> iProp) : iProp
    :=
    ∀ M, gstacks_except M out
         -∗ CLWP@{rs} e @ E {{v, ∃ N, ⌜M ⊆ N⌝ ∗ gstacks_except N out ∗ Φ v}}.
  Next Obligation.
    solve_proper.
  Qed.

  Global Typeclasses Opaque wbwp.
End wbwp.

(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'WBWP@{' re } e @ out ; E {{ Φ } }" := (wbwp re E out e Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WBWP@{' re } e @ E {{ Φ } }" := (wbwp re E ∅ e Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WBWP@{' re } e {{ Φ } }" := (wbwp re ⊤ ∅ e Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WBWP@{' re } e '@<' out >{{ Φ } }" := (wbwp re ⊤ out e Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "'WBWP@{' re } e @ out ; E {{ v , Q } }" := (wbwp re E out e (λne v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WBWP@{' re }  e  '/' @  '[' out ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WBWP@{' re } e @ E {{ v , Q } }" := (wbwp re E ∅ e (λne v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WBWP@{' re }  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WBWP@{' re } e {{ v , Q } }" := (wbwp re ⊤ ∅ e (λne v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WBWP@{' re }  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WBWP@{' re } e '@<' out >{{ v , Q } }" := (wbwp re ⊤ out e (λne v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WBWP@{' re }  e  '/' '@<'  out  >{{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Section wp.
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
  Notation istep := (internal_step rG).
  Notation isteps := (internal_steps rG).
  Notation sstep := (external_step rG).
  Notation ssteps := (external_steps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!gitreeGS_gen rs A Σ} `{!gstacksIG Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Global Instance wbwp_ne E out m :
    Proper ((dist m) ==> (dist m) ==> (dist m)) (wbwp rs E out).
  Proof.
    intros ??????; rewrite /wbwp /=.
    f_equiv; intro; simpl.
    repeat f_equiv; first done.
    intro; simpl.
    solve_proper.
  Qed.
  Global Instance wbwp_proper E out :
    Proper ((≡) ==> (≡) ==> (≡)) (wbwp rs E out).
  Proof.
    intros ??? Φ Φ' ?. apply equiv_dist=>m.
    by apply wbwp_ne; apply equiv_dist.
  Qed.

  Lemma wbwp_value_fupd' E out (Φ : ITV -n> iProp) v :
    (|={E}=> Φ v) ⊢ WBWP@{rs} (IT_of_V v) @ out; E {{ Φ }}.
  Proof.
    rewrite /wbwp; iIntros ">?" (?) "?"; iApply clwp_value_fupd';
      iExists _; iFrame; done.
  Qed.


  Lemma wbwp_val s E (Φ : ITV -n> iProp) α αv `{!IntoVal α αv}
    : (|={E}=> Φ αv) ⊢ WBWP@{rs} α @ s ; E {{ Φ }}.
  Proof.
    iIntros "G".
    rewrite -(into_val (α := α)).
    by iApply wbwp_value_fupd'.
  Qed.

  Lemma wbwp_mono E out e (Φ Ψ : ITV -n> iProp) :
    WBWP@{rs} e @ out; E {{ Φ }} -∗ (∀ v, Φ v ={E}=∗ Ψ v) -∗ WBWP@{rs} e @ out; E {{ Ψ }}.
  Proof.
    iIntros "H HΦ".
    rewrite /wbwp.
    iIntros (M) "HM".
    iApply (clwp_mono with "[H HM]"); [iApply "H"|]; [iApply "HM"|].
    iIntros (?); iDestruct 1 as (?) "[? [? ?]]".
    iMod ("HΦ" with "[$]").
    iModIntro; iExists _; iFrame.
  Qed.

  Lemma wbwp_get_gstack_full m E out e (Φ : ITV -n> iProp) :
    m ∉ out →
    gstack_exists m
    -∗ (∀ s, gstack_full m s -∗ WBWP@{rs} e @ (out ∪ {[m]}); E {{v, gstack_full m s ∗ Φ v }})
    -∗ WBWP@{rs} e @ out; E {{ Φ }}.
  Proof.
    iIntros (?) "#Hex HWBWP".
    rewrite /wbwp.
    iIntros (M) "HM".
    iDestruct (gstack_exists_in with "Hex HM") as %?.
    iDestruct (gstacks_take_out _ _ m with "Hex HM") as (s HMn) "[HM Hfl]"; first set_solver.
    iApply (clwp_wand with "[HM Hfl HWBWP]").
    { iApply ("HWBWP" with "[$] [$]"). }
    iIntros (?); iDestruct 1 as (N HNM) "(Hgs & Hfl & HΦ)".
    iDestruct (gstacks_put_back with "Hfl Hgs") as "Hgs"; first by eapply lookup_weaken; eauto.
    replace ((out ∪ {[m]}) ∖ {[m]}) with out by set_solver.
    iExists _; iFrame; done.
  Qed.

  Lemma wbwp_mend m s E out e Φ :
    gstack_full m s
    -∗ WBWP@{rs} e @ out ∖ {[m]}; E {{ Φ }}
    -∗ WBWP@{rs} e @ out; E {{v, gstack_full m s ∗ Φ v }}.
  Proof.
    iIntros "Hfl HWBWP".
    rewrite /wbwp.
    iIntros (M) "HM".
    iDestruct (gstack_full_is_out with "Hfl HM") as %?.
    iDestruct (gstacks_except_included with "HM") as "%".
    iDestruct (gstack_full_exists with "Hfl") as "#Hex".
    destruct (M !! m) as [s'|] eqn:HMns'; last by apply not_elem_of_dom in HMns'; set_solver.
    iDestruct (gstacks_out_swap _ _ m s with "HM") as "HM"; first done.
    iDestruct (gstacks_put_back with "Hfl HM") as "HM"; first by rewrite lookup_insert.
    iSpecialize ("HWBWP" with "HM").
    iApply (clwp_wand with "[$]").
    iIntros (?); iDestruct 1 as (N) "(%&HM&?)".
    iDestruct (gstacks_take_out _ _ m with "Hex HM") as (s'' HMn) "[HM Hfl]"; first set_solver.
    replace (out ∖ {[m]} ∪ {[m]}) with out; last first.
    { apply set_eq; intros p; split; [|set_solver]. destruct (decide (m = p)); set_solver. }
    iDestruct (gstacks_out_swap _ _ m s' with "HM") as "HM"; first done.
    assert (N !! m = Some s).
    { eapply lookup_weaken; last eassumption. rewrite lookup_insert //. }
    simplify_eq /=.
    iExists _; iFrame.
    iPureIntro.
    apply map_subseteq_spec.
    intros i ? HMi.
    destruct (decide (i = m)) as [->|]; first by rewrite HMns' in HMi; rewrite lookup_insert.
    rewrite lookup_insert_ne //.
    eapply lookup_weaken; last eassumption.
    rewrite lookup_insert_ne //.
  Qed.

  Lemma wbwp_make_gstack R E out e Φ :
    (∀ p, ⌜p ∉ out⌝
          -∗ gstack_full p []
          -∗ gstack_frag p [] ={E}=∗ ∃ stk, gstack_full p stk ∗ R p)
    -∗ (∀ p, ⌜p ∉ out⌝ -∗ R p -∗ WBWP@{rs} e @ out; E {{ Φ }})
    -∗ WBWP@{rs} e @ out; E {{ Φ }}.
  Proof.
    iIntros "Hstk HWP".
    rewrite /wbwp.
    iIntros (M) "HM".
    iDestruct (gstacks_except_included with "HM") as %?.
    iMod (gstack_alloc with "HM") as (m) "(%&HM&Hfr)".
    iDestruct (gstack_frag_exists with "Hfr") as "#Hex".
    iDestruct (gstacks_take_out with "Hex HM") as (s Hs) "[HM Hfl]"; first set_solver.
    rewrite lookup_insert in Hs; simplify_eq.
    iMod ("Hstk" with "[] Hfl Hfr") as (s) "[Hfl HR]"; first set_solver.
    iDestruct (gstacks_out_swap _ _ m s with "HM") as "HM"; first set_solver.
    iPoseProof (gstacks_put_back with "Hfl HM") as "HM"; first by rewrite lookup_insert.
    rewrite insert_insert.
    replace ((out ∪ {[m]}) ∖ {[m]}) with out by set_solver.
    iApply (clwp_wand with "[-]").
    { iApply ("HWP" with "[] [$] [$]"). set_solver. }
    iIntros (?); iDestruct 1 as (N HNM) "(Hgs & HΦ)".
    iExists _; iFrame.
    iPureIntro.
    etrans; last eassumption.
    apply insert_subseteq, not_elem_of_dom; done.
  Qed.

  Lemma fupd_wbwp E out e Φ :
    (|={E}=> WBWP@{rs} e @ out; E {{ Φ }}) ⊢ WBWP@{rs} e @ out; E {{ Φ }}.
  Proof. rewrite /wbwp; iIntros "H" (M) "?"; iMod "H"; iApply "H"; iAssumption. Qed.
  Lemma wbwp_fupd E out e (Φ : ITV -n> iProp) :
    WBWP@{rs} e @ out; E {{ v, |={E}=> Φ v }} ⊢ WBWP@{rs} e @ out; E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wbwp_mono E with "H"); auto.
  Qed.

  Lemma wp_wbwp E out e Φ : CLWP@{rs} e @ E {{ Φ }} -∗ WBWP@{rs} e @ out; E {{ Φ }}.
  Proof.
    iIntros "HWP".
    rewrite /wbwp.
    iIntros (M) "HM".
    iApply (clwp_wand with "HWP").
    iIntros (?) "?"; iExists _; iFrame; done.
  Qed.

  Global Instance wbwp_bind_ne s E (κ : HOM) (Φ : ITV -n> iProp)
    : NonExpansive (λ βv, (WBWP@{rs} (κ (IT_of_V βv)) @ s; E {{ Φ }})%I).
  Proof.
    solve_proper.
  Qed.

  Program Definition wbwp_bind s E (κ : HOM) e (Φ : ITV -n> iProp) :
    WBWP@{rs} e @ s; E {{ βv, WBWP@{rs} (κ (IT_of_V βv)) @ s; E {{ Φ }} }}
                ⊢ WBWP@{rs} (κ e) @ s; E {{ Φ }}.
  Proof.
    rewrite /wbwp.
    iIntros "Hwp" (M) "HM".
    iApply clwp_bind.
    iApply (clwp_wand with "[Hwp HM]"); first by iApply "Hwp".
    iIntros (?); iDestruct 1 as (?) "(%&HM&Hwp)".
    iApply (clwp_wand with "[Hwp HM]"); first by iApply "Hwp".
    iIntros (?); iDestruct 1 as (?) "(%&HM&Hwp)".
    iExists _; iFrame; iPureIntro.
    etrans; eauto.
  Qed.

  (** * Derived rules *)
  Lemma wbwp_mono' E out e (Φ Ψ : ITV -n> iProp) :
    (∀ v, Φ v ⊢ Ψ v)
    → WBWP@{rs} e @ out; E {{ Φ }} ⊢ WBWP@{rs} e @ out; E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wbwp_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.

  Lemma wbwp_frame_l E out e Φ R :
    R ∗ WBWP@{rs} e @ out; E {{ Φ }} ⊢ WBWP@{rs} e @ out; E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros "[? H]". iApply (wbwp_mono with "H").
    iIntros (?) "G".
    iModIntro.
    iFrame.
  Qed.
  Lemma wbwp_frame_r E out e Φ R :
    WBWP@{rs} e @ out; E {{ Φ }} ∗ R ⊢ WBWP@{rs} e @ out; E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "[H ?]". iApply (wbwp_mono with "H").
    iIntros (?) "G".
    iModIntro.
    iFrame.
  Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
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
  Notation istep := (internal_step rG).
  Notation isteps := (internal_steps rG).
  Notation sstep := (external_step rG).
  Notation ssteps := (external_steps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!gitreeGS_gen rs A Σ} `{!gstacksIG Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Global Instance frame_wbwp p E out e R (Φ Ψ : ITV -n> iProp) :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WBWP@{rs} e @ out; E {{ Φ }}) (WBWP@{rs} e @ out; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wbwp_frame_l. apply wbwp_mono', HR. Qed.

  Global Instance is_except_0_wbwp E out e Φ : IsExcept0 (WBWP@{rs} e @ out; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wbwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wbwp p E out e P Φ :
    ElimModal True p false (|==> P) P (WBWP@{rs} e @ out; E {{ Φ }}) (WBWP@{rs} e @ out; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wbwp.
  Qed.

  Global Instance elim_modal_fupd_wbwp p E out e P Φ :
    ElimModal True p false (|={E}=> P) P (WBWP@{rs} e @ out; E {{ Φ }}) (WBWP@{rs} e @ out; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wbwp.
  Qed.

  Global Instance add_modal_fupd_wbwp E out e P Φ :
    AddModal (|={E}=> P) P (WBWP@{rs} e @ out; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wbwp. Qed.
End proofmode_classes.
