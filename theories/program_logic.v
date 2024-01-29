(** Derived rules for program logic *)
From gitrees Require Import gitree.

Section program_logic.
  Context {sz : nat} {a : is_ctx_dep}.
  Variable rs : gReifiers a sz.
  Notation F := (gReifiers_ops a rs).
  Context {R} `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_lam (f : IT -n> IT) β s Φ `{!AsVal β} :
    ▷ WP@{rs} f β @ s {{ Φ }} ⊢ WP@{rs} Fun (Next f) ⊙ β @ s{{ Φ }}.
  Proof.
    iIntros "H".
    rewrite APP'_Fun_l.
    simpl.
    rewrite -Tick_eq.
    by iApply wp_tick.
  Qed.

End program_logic.

Section program_logic_ctx_indep.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Notation F := (gReifiers_ops NotCtxDep rs).
  Context {R} `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!invGS Σ, !stateG rs R Σ}.
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

End program_logic_ctx_indep.
