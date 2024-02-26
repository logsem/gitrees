From gitrees Require Import prelude gitree.

Section iter.
  Context {E : opsInterp}.
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Program Definition pre_iter_1 (itr : IT) : IT -n> IT -n> IT :=
    λne f α, λit β, IF α (f ⊙ (itr ⊙ f ⊙ (NATOP Nat.sub α (Ret 1)) ⊙ β)) β.
  Solve All Obligations with solve_proper_please.
  Program Definition pre_iter_2 (itr : IT) : IT -n> IT :=
    λne f, λit α, pre_iter_1 itr f α.
  Solve All Obligations with solve_proper_please.
  Program Definition pre_iter (itr : IT) : IT :=
    λit f, pre_iter_2 itr f.
    (* λit f α β, IF α (f ⊙ (itr ⊙ f ⊙ (NATOP Nat.sub α (Ret 1)) ⊙ β)) β. *)
  Solve All Obligations with solve_proper_please.

  #[local] Instance pre_iter_contractive : Contractive pre_iter.
  Proof.
    intro n.
    repeat intro. unfold pre_iter.
    repeat f_equiv. intro. simpl.
    repeat f_equiv. intro. simpl.
    f_equiv. apply Next_contractive.
    destruct n.
    { apply dist_later_0. }
    apply dist_later_S.
    apply dist_later_S in H. intro.
    simpl. solve_proper.
  Qed.
  Definition ITER : IT := fixpoint pre_iter.

  Lemma ITER_eq f α β `{!AsVal f, !AsVal α, !AsVal β}:
    ITER ⊙ f ⊙ α ⊙ β ≡ Tick_n 3 $ IF α (f ⊙ (ITER ⊙ f ⊙ (NATOP Nat.sub α (Ret 1)) ⊙ β)) β.
  Proof.
    trans (pre_iter ITER ⊙ f ⊙ α ⊙ β).
    - repeat f_equiv. apply (fixpoint_unfold pre_iter).
    - trans (Tick (pre_iter_2 ITER f ⊙ α ⊙ β)).
      { unfold pre_iter.
        rewrite -APP'_Tick_l. do 2 f_equiv.
        rewrite -APP'_Tick_l. do 2 f_equiv.
        rewrite APP'_Fun_l. cbn-[pre_iter_2].
        by rewrite Tick_eq. }
      rewrite Tick_n_S. f_equiv.
      trans (Tick (pre_iter_1 ITER f α ⊙ β)).
      { unfold pre_iter_2.
        rewrite -APP'_Tick_l. do 2 f_equiv.
        rewrite APP'_Fun_l. cbn-[pre_iter_2].
        by rewrite Tick_eq. }
      rewrite Tick_n_S. f_equiv.
      rewrite APP'_Fun_l. cbn.
      by rewrite Tick_eq.
  Qed.

End iter.

Section iter_wp.
  Context {sz : nat}.
  Variable (rs : gReifiers NotCtxDep sz).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_iter f (m : nat) β Ψ `{!AsVal f} `{!NonExpansive Ψ} :
    ⊢ WP@{rs} β {{ Ψ }} -∗
      □ (∀ βv, Ψ βv -∗ WP@{rs} (f ⊙ (IT_of_V βv)) {{ Ψ }}) -∗
      WP@{rs} (ITER ⊙ f ⊙ (Ret m) ⊙ β) {{ Ψ }}.
  Proof.
    iIntros "Hb #H".
    iApply (wp_bind _ (AppRSCtx (ITER ⊙ f ⊙ (Ret m)))).
    iApply (wp_wand with "Hb").
    iIntros (βv) "Hb". iModIntro.
    iLöb as "IH" forall (m βv).
    unfold AppRSCtx. simpl.
    rewrite ITER_eq. iApply wp_tick. iNext.
    iApply wp_tick. iNext. iApply wp_tick. iNext.
    destruct m as [|m].
    { rewrite IF_False; last lia.
      by iApply wp_val. }
    rewrite IF_True; last lia.
    iApply (wp_bind _ (AppRSCtx f)).
    iAssert ((NATOP Nat.sub (Ret (S m)) (Ret 1)) ≡ (Ret m : IT))%I as "Heq".
    { iPureIntro. rewrite (NATOP_Ret (S m) 1 Nat.sub). f_equiv.
      rewrite Nat.sub_1_r. done. }
    iRewrite "Heq".
    iSpecialize ("IH" with "Hb").
    iApply (wp_wand with "IH").
    iIntros (β'v) "Hb". iModIntro.
    unfold AppRSCtx.
    by iApply "H".
  Qed.

End iter_wp.
