(** Derived rules for program logic *)
From gitrees Require Import gitree.

Section program_logic.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Notation F := (gReifiers_ops rs).
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
  
  (* Lemma clwp_seq α β s (Φ : ITV -n> iProp) : *)
  (*   CLWP@{rs} α @ s {{ (constO (CLWP@{rs} β @ s {{ Φ }})) }} ⊢ CLWP@{rs} SEQ α β @ s {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   iApply (clwp_bind _ (SEQCtx β)). *)
  (*   iApply (clwp_wand with "H"). *)
  (*   iIntros (?) "Hb". unfold SEQCtx. *)
  (*   simpl. *)
  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ (get_val ?a) ?b] => *)
  (*       idtac *)
  (*   end. *)
  (*   simpl. *)
  (*   (* rewrite SEQ_Val. *) *)
  (* Admitted. *)

  (* Lemma clwp_let α (f : IT -n> IT) {Hf : IT_hom f} s (Φ : ITV -n> iProp) : *)
  (*   CLWP@{rs} α @ s {{ (λne αv, CLWP@{rs} f (IT_of_V αv) @ s {{ Φ }}) }} ⊢ CLWP@{rs} (LET α f) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   iApply (clwp_bind _ (LETCTX f)). *)
  (*   iApply (clwp_wand with "H"). *)
  (*   iIntros (?) "Hb". simpl. *)
  (*   (* by rewrite LET_Val. *) *)
  (* Admitted. *)

End program_logic.
