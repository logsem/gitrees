(* This file is copied and adapted from the weakestpre file in the iris development. *)

From stdpp Require Export coPset.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From gitrees Require Export prelude gitree lang_generic hom.
Require Export gitrees.gitree.weakestpre.
From gitrees Require Export examples.delim_lang.clwp examples.delim_lang.program_logic.ghost_stacks.
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
  Notation istep := (istep rG).
  Notation isteps := (isteps rG).
  Notation sstep := (sstep rG).
  Notation ssteps := (ssteps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!invGS Σ} `{!stateG rs A Σ}.
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

(* (* Texan triples *) *)
(* Notation "'{WB{{' P } } } e @ out ; E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e @ out; E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' out ;  '/' E  ']' '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'{WB{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e @ E {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'{WB{{' P } } } e '@<' out >{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e @ out {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' '@<'  out  >{{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'{WB{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, *)
(*       P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e {{ Φ }})%I *)
(*     (at level 20, x closed binder, y closed binder, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)

(* Notation "'{WB{{' P } } } e @ out ; E {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e @ out; E {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' @  '[' out ;  '/' E  ']' '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'{WB{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e @ E {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' @  E  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'{WB{{' P } } } e '@<' out >{{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e @ out {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' '@<'  out  >{{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)
(* Notation "'{WB{{' P } } } e {{{ 'RET' pat ; Q } } }" := *)
(*   (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e {{ Φ }})%I *)
(*     (at level 20, *)
(*      format "'[hv' {WB{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope. *)

(* (** Aliases for stdpp scope -- they inherit the levels and format from above. *) *)
(* Notation "'{WB{{' P } } } e @ out ; E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e @ out; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e @ E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e '@<' out >{{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e @< out >{{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WBWP e {{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e @ out ; E {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e @ out; E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e @ E {{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e @< out > {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e @< out >{{ Φ }}) : stdpp_scope. *)
(* Notation "'{WB{{' P } } } e {{{ 'RET' pat ; Q } } }" := *)
(*   (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WBWP e {{ Φ }}) : stdpp_scope. *)

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
  Notation istep := (istep rG).
  Notation isteps := (isteps rG).
  Notation sstep := (sstep rG).
  Notation ssteps := (ssteps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!invGS Σ} `{!stateG rs A Σ} `{!gstacksIG Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Global Instance wbwp_ne E out e m :
    Proper ((dist m) ==> (dist m)) (wbwp rs E out e).
  Proof.
    intros ???; rewrite /wbwp /=.
    repeat f_equiv.
    intro; simpl.
    f_equiv.
    intro; simpl.
    f_equiv.
    solve_proper.
  Qed.
  Global Instance wbwp_proper E out e :
    Proper ((≡) ==> (≡)) (wbwp rs E out e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>m; apply wbwp_ne=>v; apply equiv_dist.
  Qed.

  Lemma wbwp_value_fupd' E out (Φ : ITV -n> iProp) v :
    (|={E}=> Φ v) ⊢ WBWP@{rs} (IT_of_V v) @ out; E {{ Φ }}.
  Proof.
    rewrite /wbwp; iIntros ">?" (?) "?"; iApply clwp_value_fupd';
      iExists _; iFrame; done.
  Qed.

  (* Lemma wbwp_strong_mono E1 E2 out e Φ Ψ : *)
  (*   E1 ⊆ E2 → *)
  (*   WBWP e @ out; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WBWP e @ out; E2 {{ Ψ }}. *)
  (* Proof. *)
  (*   iIntros (HE) "H HΦ". *)
  (*   rewrite /wbwp. *)
  (*   iIntros (M) "HM". *)
  (*   iApply (wp_strong_mono with "[H HM]"); [done|eassumption|by iApply "H"|]. *)
  (*   iIntros (?); iDestruct 1 as (?) "[? [? ?]]". *)
  (*   iMod ("HΦ" with "[$]"). *)
  (*   iModIntro; iExists _; iFrame. *)
  (* Qed. *)

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

  (* Lemma wp_atomic E1 E2 out e Φ `{!Atomic WeaklyAtomic e} : *)
  (*   (|={E1,E2}=> WBWP e @ out; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WBWP e @ out; E1 {{ Φ }}. *)
  (* Proof. *)
  (*   rewrite /wbwp; iIntros "H" (M) "HM". *)
  (*   iApply wp_atomic. *)
  (*   iMod "H"; iModIntro. *)
  (*   iApply (wp_wand with "[H HM]"); first by iApply "H". *)
  (*   iIntros (?); iDestruct 1 as (?) "(?&?&>?)". *)
  (*   iModIntro; iExists _; iFrame. *)
  (* Qed. *)

  Lemma wp_wbwp E out e Φ : CLWP@{rs} e @ E {{ Φ }} -∗ WBWP@{rs} e @ out; E {{ Φ }}.
  Proof.
    iIntros "HWP".
    rewrite /wbwp.
    iIntros (M) "HM".
    iApply (clwp_wand with "HWP").
    iIntros (?) "?"; iExists _; iFrame; done.
  Qed.

  (* (** This lemma gives us access to the later credits that are generated in each step, *)
  (* assuming that we have instantiated [num_laters_per_step] with a non-trivial (e.g. linear) *)
  (* function. *)
  (* This lemma can be used to provide a "regeneration" mechanism for later credits. *)
  (* [state_interp] will have to be defined in a way that involves the required regneration *)
  (* tokens. TODO: point to an example of how this is used. *)

  (* In detail, a client can use this lemma as follows: *)
  (* - the client obtains the state interpretation [state_interp _ ns _ _], *)
  (* - it uses some ghost state wired up to the interpretation to know that *)
  (*   [ns = k + m], and update the state interpretation to [state_interp _ m _ _], *)
  (* - _after_ [e] has finally stepped, we get [num_laters_per_step k] later credits *)
  (*   that we can use to prove [P] in the postcondition, and we have to update *)
  (*   the state interpretation from [state_interp _ (S m) _ _] to *)
  (*   [state_interp _ (S ns) _ _] again. *) *)
  (* Lemma wbwp_credit_access E out e Φ P : *)
  (*   TCEq (to_val e) None → *)
  (*   (∀ m k, num_laters_per_step m + num_laters_per_step k ≤ num_laters_per_step (m + k)) → *)
  (*   (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗ *)
  (*                                                   ∃ k m, state_interp σ1 m κs nt ∗ ⌜ns = (m + k)%nat⌝ ∗ *)
  (*                                                                                            (∀ nt σ2 κs, £ (num_laters_per_step k) -∗ state_interp σ2 (S m) κs nt ={E}=∗ *)
  (*                                                                                                                                                                         state_interp σ2 (S ns) κs nt ∗ P)) -∗ *)
  (*                                                                                                                                                                                                               WBWP e @ out; E {{ v, P ={E}=∗ Φ v }} -∗ *)
  (*                                                                                                                                                                                                                                                        WBWP e @ out; E {{ Φ }}. *)
  (* Proof. *)
  (*   rewrite /wbwp. *)
  (*   iIntros (? ?) "Hupd Hwp". *)
  (*   iIntros (M) "HM". *)
  (*   iApply (wp_credit_access with "Hupd"); first done. *)
  (*   iApply (wp_wand with "[Hwp HM]"); first by iApply "Hwp". *)
  (*   iIntros (?); iDestruct 1 as (?) "(?&?&H)". *)
  (*   iIntros "HP"; iMod ("H" with "HP"). *)
  (*   iModIntro; iExists _; iFrame. *)
  (* Qed. *)

  (* (** In this stronger version of [wp_step_fupdN], the masks in the *)
  (*  step-taking fancy update are a bit weird and somewhat difficult to *)
  (*  use in practice. Hence, we prove it for the sake of completeness, *)
  (*  but [wp_step_fupdN] is just a little bit weaker, suffices in *)
  (*  practice and is easier to use. *)

  (*  See the statement of [wp_step_fupdN] below to understand the use of *)
  (*  ordinary conjunction here. *) *)
  (* Lemma wbwp_step_fupdN_strong k E1 E2 out e P Φ : *)
  (*   TCEq (to_val e) None → E2 ⊆ E1 → *)
  (*   (∀ σ ns κs nt, state_interp σ ns κs nt *)
  (*                  ={E1,∅}=∗ ⌜k ≤ S (num_laters_per_step ns)⌝) ∧ *)
  (*     ((|={E1,E2}=> |={∅}▷=>^k |={E2,E1}=> P) ∗ *)
  (*        WBWP e @ out; E2 {{ v, P ={E1}=∗ Φ v }}) -∗ *)
  (*                                                    WBWP e @ out; E1 {{ Φ }}. *)
  (* Proof. *)
  (*   rewrite /wbwp. *)
  (*   iIntros (? ?) "Hwp". *)
  (*   iIntros (M) "HM". *)
  (*   iApply (wp_step_fupdN_strong); first done. *)
  (*   iSplit; first iDestruct "Hwp" as "[$ _]". *)
  (*   iDestruct "Hwp" as "[_ [$ Hwp]]". *)
  (*   iApply (wp_wand with "[Hwp HM]"); first by iApply "Hwp". *)
  (*   iIntros (?); iDestruct 1 as (?) "(?&?&H)". *)
  (*   iIntros "HP"; iMod ("H" with "HP"). *)
  (*   iModIntro; iExists _; iFrame. *)
  (* Qed. *)

  Global Instance wbwp_bind_ne s E (κ : HOM) (Φ : ITV -n> iProp)
    : NonExpansive (λ βv, (WBWP@{rs} (`κ (IT_of_V βv)) @ s; E {{ Φ }})%I).
  Proof.
    solve_proper.
  Qed.

  Program Definition wbwp_bind s E (κ : HOM) e (Φ : ITV -n> iProp) :
    WBWP@{rs} e @ s; E {{ βv, WBWP@{rs} (`κ (IT_of_V βv)) @ s; E {{ Φ }} }}
                ⊢ WBWP@{rs} (`κ e) @ s; E {{ Φ }}.
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

  (* The following lemma does not work for well-bracketed weakest preconditions. *)
  (* The reason is that it could be that the stack is broken across evaluation context and is only *)
  (* going to be mended afterwards. *)
  (* Lemma wbwp_bind_inv K `{!LanguageCtx K} E out e Φ : *)
  (*   WBWP K e @ out; E {{ Φ }} ⊢ WBWP e @ out; E {{ v, WBWP K (of_val v) @ out; E {{ Φ }} }}. *)

  (** * Derived rules *)
  Lemma wbwp_mono' E out e (Φ Ψ : ITV -n> iProp) :
    (∀ v, Φ v ⊢ Ψ v)
    → WBWP@{rs} e @ out; E {{ Φ }} ⊢ WBWP@{rs} e @ out; E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wbwp_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.

  (* Lemma wp_stuck_mono s1 s2 E e Φ : *)
  (*   s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}. *)
  (* Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed. *)
  (* Lemma wp_stuck_weaken s E e Φ : *)
  (*   WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}. *)
  (* Proof. apply wp_stuck_mono. by destruct s. Qed. *)

  (* Lemma wb_mask_mono E1 E2 out e Φ : E1 ⊆ E2 → WBWP e @ out; E1 {{ Φ }} ⊢ WBWP e @ out; E2 {{ Φ }}. *)
  (* Proof. iIntros (?) "H"; iApply (wbwp_strong_mono with "H"); auto. Qed. *)
  (* Global Instance wbwp_mono' E out e : *)
  (*   Proper (pointwise_relation _ (⊢) ==> (⊢)) (wbwp E out e). *)
  (* Proof. by intros Φ Φ' ?; apply wbwp_mono. Qed. *)
  (* Global Instance wbwp_flip_mono' E out e : *)
  (*   Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wbwp E out e). *)
  (* Proof. by intros Φ Φ' ?; apply wbwp_mono. Qed. *)






  (* Lemma wbwp_value_fupd s E Φ e v : IntoVal e v → (|={E}=> Φ v) -∗ WBWP e @ s; E {{ Φ }}. *)
  (* Proof. intros <-. by iApply wbwp_value_fupd'. Qed. *)
  (* Lemma wbwp_value' E out Φ v : Φ v ⊢ WBWP (of_val v) @ out; E {{ Φ }}. *)
  (* Proof. rewrite -wbwp_value_fupd'; auto. Qed. *)
  (* Lemma wbwp_value E out Φ e v : IntoVal e v → Φ v ⊢ WBWP e @ out; E {{ Φ }}. *)
  (* Proof. intros <-. apply wbwp_value'. Qed. *)

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

  (* (** This lemma states that if we can prove that [n] laters are used in *)
  (*  the current physical step, then one can perform an n-steps fancy *)
  (*  update during that physical step. The resources needed to prove the *)
  (*  bound on [n] are not used up: they can be reused in the proof of *)
  (*  the WP or in the proof of the n-steps fancy update. In order to *)
  (*  describe this unusual resource flow, we use ordinary conjunction as *)
  (*  a premise. *) *)
  (* Lemma wbwp_step_fupdN n E1 E2 out e P Φ : *)
  (*   TCEq (to_val e) None → E2 ⊆ E1 → *)
  (*   (∀ σ ns κs nt, state_interp σ ns κs nt *)
  (*                  ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧ *)
  (*     ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗ *)
  (*        WBWP e @ out; E2 {{ v, P ={E1}=∗ Φ v }}) -∗ *)
  (*                                                    WBWP e @ out; E1 {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (??) "H". iApply (wbwp_step_fupdN_strong with "[H]"); [done|]. *)
  (*   iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP". *)
  (*   iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|]. *)
  (*   iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first. *)
  (*   { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. } *)
  (*   iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H". *)
  (*   iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|]. *)
  (*   by rewrite difference_empty_L (comm_L (∪)) -union_difference_L. *)
  (* Qed. *)
  (* Lemma wbwp_step_fupd E1 E2 out e P Φ : *)
  (*   TCEq (to_val e) None → E2 ⊆ E1 → *)
  (*   (|={E1}[E2]▷=> P) -∗ WBWP e @ out; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WBWP e @ out; E1 {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (??) "HR H". *)
  (*   iApply (wbwp_step_fupdN_strong 1 E1 E2 with "[-]"); [done|..]. iSplit. *)
  (*   - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|]. *)
  (*     auto with lia. *)
  (*   - iFrame "H". iMod "HR" as "$". auto. *)
  (* Qed. *)

  (* Lemma wbwp_frame_step_l E1 E2 out e Φ R : *)
  (*   TCEq (to_val e) None → E2 ⊆ E1 → *)
  (*   (|={E1}[E2]▷=> R) ∗ WBWP e @ out; E2 {{ Φ }} ⊢ WBWP e @ out; E1 {{ v, R ∗ Φ v }}. *)
  (* Proof. *)
  (*   iIntros (??) "[Hu Hwp]". iApply (wbwp_step_fupd with "Hu"); try done. *)
  (*   iApply (wbwp_mono with "Hwp"). by iIntros (?) "$$". *)
  (* Qed. *)
  (* Lemma wbwp_frame_step_r E1 E2 out e Φ R : *)
  (*   TCEq (to_val e) None → E2 ⊆ E1 → *)
  (*   WBWP e @ out; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WBWP e @ out; E1 {{ v, Φ v ∗ R }}. *)
  (* Proof. *)
  (*   rewrite [(WBWP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R). *)
  (*   apply wbwp_frame_step_l. *)
  (* Qed. *)
  (* Lemma wbwp_frame_step_l' E out e Φ R : *)
  (*   TCEq (to_val e) None → ▷ R ∗ WBWP e @ out; E {{ Φ }} ⊢ WBWP e @ out; E {{ v, R ∗ Φ v }}. *)
  (* Proof. iIntros (?) "[??]". iApply (wbwp_frame_step_l E E); try iFrame; eauto. Qed. *)
  (* Lemma wbwp_frame_step_r' E out e Φ R : *)
  (*   TCEq (to_val e) None → WBWP e @ out; E {{ Φ }} ∗ ▷ R ⊢ WBWP e @ out; E {{ v, Φ v ∗ R }}. *)
  (* Proof. iIntros (?) "[??]". iApply (wbwp_frame_step_r E E out); try iFrame; eauto. Qed. *)

  (* Lemma wbwp_wand E out e Φ Ψ : *)
  (*   WBWP e @ out; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WBWP e @ out; E {{ Ψ }}. *)
  (* Proof. *)
  (*   iIntros "Hwp H". iApply (wbwp_strong_mono with "Hwp"); auto. *)
  (*   iIntros (?) "?". by iApply "H". *)
  (* Qed. *)
  (* Lemma wbwp_wand_l E out e Φ Ψ : *)
  (*   (∀ v, Φ v -∗ Ψ v) ∗ WBWP e @ out; E {{ Φ }} ⊢ WBWP e @ out; E {{ Ψ }}. *)
  (* Proof. iIntros "[H Hwp]". iApply (wbwp_wand with "Hwp H"). Qed. *)
  (* Lemma wbwp_wand_r E out e Φ Ψ : *)
  (*   WBWP e @ out; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WBWP e @ out; E {{ Ψ }}. *)
  (* Proof. iIntros "[Hwp H]". iApply (wbwp_wand with "Hwp H"). Qed. *)
  (* Lemma wp_frame_wand E out e Φ R : *)
  (*   R -∗ WBWP e @ out; E {{ v, R -∗ Φ v }} -∗ WBWP e @ out; E {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "HR HWP". iApply (wbwp_wand with "HWP"). *)
  (*   iIntros (v) "HΦ". by iApply "HΦ". *)
  (* Qed. *)
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
  Notation istep := (istep rG).
  Notation isteps := (isteps rG).
  Notation sstep := (sstep rG).
  Notation ssteps := (ssteps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!invGS Σ} `{!stateG rs A Σ} `{!gstacksIG Σ}.
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

  (* Global Instance elim_modal_fupd_wbwp_atomic p E1 E2 out e P Φ : *)
  (*   ElimModal (Atomic WeaklyAtomic e) p false *)
  (*     (|={E1,E2}=> P) P *)
  (*     (WBWP e @ out; E1 {{ Φ }}) (WBWP e @ out; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100. *)
  (* Proof. *)
  (*   intros ?. by rewrite intuitionistically_if_elim *)
  (*               fupd_frame_r wand_elim_r wp_atomic. *)
  (* Qed. *)

  Global Instance add_modal_fupd_wbwp E out e P Φ :
    AddModal (|={E}=> P) P (WBWP@{rs} e @ out; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wbwp. Qed.

  (* Global Instance elim_acc_wbwp_atomic {X} E1 E2 α β γ out e Φ : *)
  (*   ElimAcc (X:=X) (Atomic WeaklyAtomic e) *)
  (*     (fupd E1 E2) (fupd E2 E1) *)
  (*     α β γ (WBWP e @ out; E1 {{ Φ }}) *)
  (*     (λ x, WBWP e @ out; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100. *)
  (* Proof. *)
  (*   iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply (wbwp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)

  (* Global Instance elim_acc_wbwp_nonatomic {X} E α β γ out e Φ : *)
  (*   ElimAcc (X:=X) True (fupd E E) (fupd E E) *)
  (*     α β γ (WBWP@{rs} e @ out; E {{ Φ }}) *)
  (*     (λ x, WBWP@{rs} e @ out; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply wbwp_fupd. *)
  (*   iApply (wbwp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)
End proofmode_classes.
