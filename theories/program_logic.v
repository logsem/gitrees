(** Derived rules for program logic *)
From gitrees Require Import gitree.

Section program_logic.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).

  Context `{!invGS Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_seq α β Φ `{!NonExpansive Φ} :
    WP@{rs} α {{ _, WP@{rs} β {{ Φ }} }} ⊢ WP@{rs} (SEQ α β) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_bind _ (SEQCtx β)).
    iApply (wp_wand with "H").
    iIntros (?) "Hb". unfold SEQCtx.
    by rewrite SEQ_Val.
  Qed.

  Lemma wp_let α (f : IT -n> IT) Φ `{!NonExpansive Φ} :
    WP@{rs} α {{ αv, WP@{rs} f (IT_of_V αv) {{ Φ }} }} ⊢ WP@{rs} (LET α f) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_bind _ (LETCTX f)).
    iApply (wp_wand with "H").
    iIntros (?) "Hb". simpl.
    by rewrite LET_Val.
  Qed.

  Lemma wp_lam (f : IT -n> IT) β Φ `{!AsVal β} :
    ▷ WP@{rs} f β {{ Φ }} ⊢ WP@{rs} Fun (Next f) ⊙ β {{ Φ }}.
  Proof.
    rewrite APP'_Fun_l.
    rewrite -Tick_eq/=. iApply wp_tick.
  Qed.


End program_logic.

