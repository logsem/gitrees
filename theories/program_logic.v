(** Derived rules for program logic *)
From gitrees Require Import gitree.

Section program_logic.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F natO).
  Notation ITV := (ITV F natO).

  Context `{!invGS Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_seq α β s Φ `{!NonExpansive Φ} :
    WP@{rs} α @ s {{ _, WP@{rs} β @ s {{ Φ }} }} ⊢ WP@{rs} SEQ α β @ s {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_bind _ (SEQCtx β)).
    iApply (wp_wand with "H").
    iIntros (?) "Hb". unfold SEQCtx.
    by rewrite SEQ_Val.
  Qed.

  Lemma wp_let α (f : IT -n> IT) s Φ `{!NonExpansive Φ} :
    WP@{rs} α @ s {{ αv, WP@{rs} f (IT_of_V αv) @ s {{ Φ }} }} ⊢ WP@{rs} (LET α f) @ s {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_bind _ (LETCTX f)).
    iApply (wp_wand with "H").
    iIntros (?) "Hb". simpl.
    by rewrite LET_Val.
  Qed.

  Lemma wp_lam (f : IT -n> IT) β s Φ `{!AsVal β} :
    ▷ WP@{rs} f β @ s {{ Φ }} ⊢ WP@{rs} Fun (Next f) ⊙ β @ s{{ Φ }}.
  Proof.
    rewrite APP'_Fun_l.
    rewrite -Tick_eq/=. iApply wp_tick.
  Qed.


End program_logic.

