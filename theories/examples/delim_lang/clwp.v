From stdpp Require Export coPset.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From gitrees Require Export prelude gitree lang_generic hom.
Require Export gitrees.gitree.weakestpre.
Import uPred.

Section clwp.
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

  Program Definition clwp s E : IT -> (ITV -n> iProp) -> iProp :=
    λ α Φ, (∀ (κ : HOM) (Ψ : ITV -n> iProp),
              (∀ v, Φ v
                    -∗ WP@{rs} (`κ (IT_of_V v)) @ s ; E {{ Ψ }})
              -∗ WP@{rs} (`κ α) @ s ; E {{ Ψ }})%I.

  Notation "'CLWP' e @ s ; E {{ Φ } }" :=
    (clwp s E e Φ)
      (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'CLWP' e @ E {{ Φ } }" :=
    (clwp notStuck E e Φ)
      (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'CLWP' e {{ Φ } }" :=
    (clwp notStuck ⊤ e Φ)
      (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'CLWP' e @ s ; E {{ v , Q } }" :=
    (clwp s E e (λne v, Q))
      (at level 20, e, Q at level 200,
        format "'[hv' 'CLWP'  e  '/' @  s ';' E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
      : bi_scope.
  Notation "'CLWP' e @ E {{ v , Q } }" :=
    (clwp notStuck E e (λne v, Q))
      (at level 20, e, Q at level 200,
        format "'[hv' 'CLWP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
      : bi_scope.
  Notation "'CLWP' e {{ v , Q } }" :=
    (clwp notStuck ⊤ e (λne v, Q))
      (at level 20, e, Q at level 200,
        format "'[hv' 'CLWP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
      : bi_scope.
  Notation "'CLWP' e @ s ; E {{ Φ } }" :=
    (clwp s E e Φ)
      (at level 20, e, Φ at level 200,
        format "'[hv' 'CLWP'  e  '/' @  s ';' E  '/' {{  '[' Φ ']'  } } ']'")
      : bi_scope.
  Notation "'CLWP' e @ E {{ Φ } }" :=
    (clwp notStuck E e Φ)
      (at level 20, e, Φ at level 200,
        format "'[hv' 'CLWP'  e  '/' @  E  '/' {{  '[' Φ ']'  } } ']'")
      : bi_scope.
  Notation "'CLWP' e {{ Φ } }" :=
    (clwp notStuck ⊤ e Φ)
      (at level 20, e, Φ at level 200,
        format "'[hv' 'CLWP'  e  '/' {{  '[' Φ ']'  } } ']'")
      : bi_scope.

  Global Typeclasses Opaque clwp.

  Global Instance clwp_ne s E m :
    Proper (dist m ==> dist m ==> dist m) (clwp s E).
  Proof. solve_proper. Qed.
  Global Instance clwp_proper s E :
    Proper ((≡) ==> (≡) ==> (≡)) (clwp s E).
  Proof. solve_proper. Qed.

  Lemma clwp_value_fupd' s E (Φ : ITV -n> iProp) v
    : (|={E}=> Φ v) ⊢ CLWP (IT_of_V v) @ s ; E {{ Φ }}.
  Proof.
    rewrite /clwp; iIntros "G" (??) "H".
    iMod "G".
    by iApply "H".
  Qed.

  Lemma clwp_mono s E e (Φ Ψ : ITV -n> iProp) :
    CLWP e @ s; E {{ Φ }} -∗ (∀ v, Φ v ={E}=∗ Ψ v) -∗ CLWP e @ s; E {{ Ψ }}.
  Proof.
    iIntros "H HΦ".
    rewrite /clwp.
    iIntros (κ Θ) "J".
    iApply "H".
    iIntros (?) "G".
    iMod ("HΦ" with "G").
    by iApply "J".
  Qed.

  Lemma fupd_clwp s E e Φ :
    (|={E}=> CLWP e @ s; E {{ Φ }}) ⊢ CLWP e @ s; E {{ Φ }}.
  Proof.
    rewrite /clwp; iIntros "H" (κ Θ) "J".
    iMod "H"; iApply "H"; iAssumption.
  Qed.

  Lemma clwp_fupd s E e (Φ : ITV -n> iProp) :
    CLWP e @ s; E {{ v, |={E}=> Φ v }} ⊢ CLWP e @ s; E {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite /clwp; iIntros (κ Θ) "J".
    iApply "H".
    iIntros (v) "G".
    iMod "G".
    by iApply "J".
  Qed.

  Lemma clwp_wp s E e (Φ : ITV -n> iProp) :
    CLWP e @ s; E {{ Φ }} -∗ WP@{rs} e @ s; E {{ Φ }}.
  Proof.
    iIntros "HWP".
    rewrite /clwp.
    iApply ("HWP" $! HOM_id).
    iIntros (?) "?".
    by iApply wp_val.
  Qed.

  Global Instance clwp_bind_ne s E (κ : HOM) (Φ : ITV -n> iProp)
    : NonExpansive (λ βv, (CLWP (`κ (IT_of_V βv)) @ s; E {{ Φ }})%I).
  Proof.
    solve_proper.
  Qed.

  Program Definition clwp_bind s E (κ : HOM) e (Φ : ITV -n> iProp) :
    CLWP e @ s; E {{ βv, CLWP (`κ (IT_of_V βv)) @ s; E {{ Φ }} }}
                ⊢ CLWP (`κ e) @ s; E {{ Φ }}.
  Proof.
    rewrite /clwp.
    iIntros "H %κ' %Ψ G".
    rewrite HOM_ccompose.
    iApply ("H" $! (HOM_compose κ' κ)).
    iIntros (v) "J".
    iApply "J".
    iIntros (v') "K".
    by iApply "G".
  Qed.

  Lemma clwp_wand s E e (Φ Ψ : ITV -n> iProp) :
    CLWP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ CLWP e @ s; E {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (clwp_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma clwp_wand_l s E e (Φ Ψ : ITV -n> iProp) :
    (∀ v, Φ v -∗ Ψ v) ∗ CLWP e @ s; E {{ Φ }} ⊢ CLWP e @ s; E {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (clwp_wand with "Hwp H"). Qed.
  Lemma clwp_wand_r s E e (Φ Ψ : ITV -n> iProp) :
    CLWP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ CLWP e @ s; E {{ Ψ }}.
  Proof. iIntros "[Hwp H]". iApply (clwp_wand with "Hwp H"). Qed.

End clwp.

Check clwp.

Notation "'CLWP@{' re } e @ s ; E {{ Φ } }" :=
  (clwp re s E e Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'CLWP@{' re } e @ E {{ Φ } }" :=
  (clwp re notStuck E e Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'CLWP@{' re } e {{ Φ } }" :=
  (clwp re notStuck ⊤ e Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'CLWP@{' re } e @ s ; E {{ v , Q } }" :=
  (clwp re s E e (λne v, Q))
    (at level 20, e, Q at level 200,
      format "'[hv' 'CLWP@{' re }  e  '/' @  s ';' E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.
Notation "'CLWP@{' re } e @ E {{ v , Q } }" :=
  (clwp re notStuck E e (λne v, Q))
    (at level 20, e, Q at level 200,
      format "'[hv' 'CLWP@{' re }  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.
Notation "'CLWP@{' re } e {{ v , Q } }" :=
  (clwp re notStuck ⊤ e (λne v, Q))
    (at level 20, e, Q at level 200,
      format "'[hv' 'CLWP@{' re }  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.
Notation "'CLWP@{' re } e @ s ; E {{ Φ } }" :=
  (clwp re s E e Φ)
    (at level 20, e, Φ at level 200,
      format "'[hv' 'CLWP@{' re }  e  '/' @  s ';' E  '/' {{  '[' Φ ']'  } } ']'")
    : bi_scope.
Notation "'CLWP@{' re } e @ E {{ Φ } }" :=
  (clwp re notStuck E e Φ)
    (at level 20, e, Φ at level 200,
      format "'[hv' 'CLWP@{' re }  e  '/' @  E  '/' {{  '[' Φ ']'  } } ']'")
    : bi_scope.
Notation "'CLWP@{' re } e {{ Φ } }" :=
  (clwp re notStuck ⊤ e Φ)
    (at level 20, e, Φ at level 200,
      format "'[hv' 'CLWP@{' re }  e  '/' {{  '[' Φ ']'  } } ']'")
    : bi_scope.

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

  Context `{!invGS Σ} `{!stateG rs A Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  Global Instance frame_clwp p E s e R (Φ Ψ : ITV -n> iProp) :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (CLWP@{rs} e @ s; E {{ Φ }}) (CLWP@{rs} e @ s; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR.
    iIntros "(H1 & H2)".
    iApply (clwp_wand with "H2"); first last.
    iIntros (?) "H3".
    iApply HR.
    iFrame "H1 H3".
  Qed.

  Global Instance is_except_0_clwp E s e Φ : IsExcept0 (CLWP@{rs} e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_clwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_clwp p E s e P Φ :
    ElimModal True p false (|==> P) P (CLWP@{rs} e @ s; E {{ Φ }}) (CLWP@{rs} e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_clwp.
  Qed.

  Global Instance elim_modal_fupd_clwp p E s e P Φ :
    ElimModal True p false (|={E}=> P) P (CLWP@{rs} e @ s; E {{ Φ }}) (CLWP@{rs} e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_clwp.
  Qed.

  Global Instance add_modal_fupd_clwp E s e P Φ :
    AddModal (|={E}=> P) P (CLWP@{rs} e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_clwp. Qed.

End proofmode_classes.
