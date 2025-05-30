(** Encoding of pairs *)
From gitrees Require Import prelude.
From gitrees.gitree Require Import core lambda.

Section pairs.
  Context {E : opsInterp}.
  Context {A : ofe} `{!Cofe A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Program Definition pairITV : IT -n> IT -n> IT := λne a b,
      λit f, f ⊙ a ⊙ b.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Program Definition pairIT : IT -n> IT -n> IT := λne a b,
      get_val (λne v2, get_val (λne v1, pairITV v1 v2) a) b.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

  Program Definition projIT1f : IT := λit a b, a.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Program Definition projIT1 : IT -n> IT := λne t, t ⊙ projIT1f.

  Program Definition projT2f : IT := λit a b, b.
  Program Definition projIT2 : IT -n> IT := λne t, t ⊙ projT2f.

  Lemma pairT_tick_r α β : pairIT α (Tick β) ≡ Tick $ pairIT α β.
  Proof. unfold pairIT. rewrite get_val_tick//. Qed.
  Lemma pairT_tick_l α β `{!AsVal β} :
    pairIT (Tick α) β ≡ Tick $ pairIT α β.
  Proof. unfold pairIT. rewrite !get_val_ITV /= get_val_tick//. Qed.
  Lemma pairT_vis_r α op i k :
    pairIT α (Vis op i k) ≡ Vis op i (laterO_map (pairIT α) ◎ k).
  Proof.
    unfold pairIT. rewrite get_val_vis. f_equiv.
    intro x. simpl. done.
  Qed.
  Lemma pairT_vis_l β op i k `{!AsVal β} :
    pairIT (Vis op i k) β ≡ Vis op i (laterO_map (flipO pairIT β) ◎ k).
  Proof.
    unfold pairIT. simpl. rewrite get_val_ITV/=.
    rewrite get_val_vis. f_equiv. f_equiv. f_equiv.
    intro x. simpl. rewrite get_val_ITV/=. done.
  Qed.

  Lemma projIT1_tick α : projIT1 (Tick α) ≡ Tick $ projIT1 α.
  Proof. simpl. by rewrite APP'_Tick_l. Qed.
  Lemma projIT1_vis op i k : projIT1 (Vis op i k) ≡ Vis op i (laterO_map projIT1 ◎ k).
  Proof.
    simpl. rewrite APP'_Vis_l.
    repeat f_equiv. intro x. simpl. reflexivity.
  Qed.
  Lemma projIT2_tick α : projIT2 (Tick α) ≡ Tick $ projIT2 α.
  Proof. simpl. by rewrite APP'_Tick_l. Qed.
  Lemma projIT2_vis op i k : projIT2 (Vis op i k) ≡ Vis op i (laterO_map projIT2 ◎ k).
  Proof.
    simpl. rewrite APP'_Vis_l.
    repeat f_equiv. intro x. simpl. reflexivity.
  Qed.

  Lemma projIT1_pairV α β `{!AsVal α, !AsVal β} : projIT1 (pairITV α β) ≡ Tick_n 3 α.
  Proof.
    simpl.
    rewrite APP'_Fun_l /=.
    rewrite -Tick_eq. f_equiv.
    set (f :=  λit _, α).
    trans (APP' (Tick f) β).
    { f_equiv.
      rewrite APP'_Fun_l/=.
      rewrite -Tick_eq. f_equiv.
      unfold f. f_equiv.
      intro. simpl. reflexivity. }
    rewrite /f. rewrite APP'_Tick_l.
    f_equiv. rewrite APP'_Fun_l/=.
    rewrite -Tick_eq/=//.
  Qed.
  Lemma projIT1_pair α β `{!AsVal α, !AsVal β} : projIT1 (pairIT α β) ≡ Tick_n 3 α.
  Proof.
    cbn-[pairITV].
    simpl.
    trans (APP' (pairITV α β) projIT1f).
    { f_equiv. rewrite get_val_ITV/=.
      rewrite get_val_ITV/=. done. }
    by apply projIT1_pairV.
  Qed.

  Lemma projIT2_pairV α β `{!AsVal α, !AsVal β} : projIT2 (pairITV α β) ≡ Tick_n 3 β.
  Proof.
    cbn-[pairITV].
    simpl.
    rewrite APP'_Fun_l/= -Tick_eq.
    f_equiv.
    etrans.
    { apply APP'_Proper; last reflexivity. rewrite APP'_Fun_l/=.
      rewrite -Tick_eq. reflexivity. }
    rewrite APP'_Tick_l. f_equiv.
    rewrite APP'_Fun_l/=. by rewrite Tick_eq.
  Qed.

  Lemma projIT2_pair α β `{!AsVal α, !AsVal β} : projIT2 (pairIT α β) ≡ Tick_n 3 β.
  Proof.
    cbn-[pairITV].
    simpl.
    trans (APP' (pairITV α β) projT2f).
    { f_equiv. rewrite get_val_ITV /=.
      rewrite get_val_ITV/=. done. }
    by apply projIT2_pairV.
  Qed.

  #[global] Instance projIT1_hom : IT_hom projIT1.
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intros a. apply projIT1_tick.
    - intros op i k. rewrite projIT1_vis.
      reflexivity.
    - intros e. simpl.
      by rewrite APP'_Err_l.
  Qed.
  #[global] Instance projIT2_hom : IT_hom projIT2.
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intros a. apply projIT2_tick.
    - intros op i k. rewrite projIT2_vis.
      reflexivity.
    - intros e. simpl.
      by rewrite APP'_Err_l.
  Qed.

  Definition PairRSCtx α : IT -n> IT := pairIT α.
  Program Definition PairLSCtx β `{!AsVal β} : IT -n> IT := λne α, pairIT α β.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

  #[global] Instance PairRSCtx_hom α : IT_hom (PairRSCtx α).
  Proof.
    unfold PairRSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intros a. apply pairT_tick_r.
    - intros op i k. rewrite pairT_vis_r.
      reflexivity.
    - intros e. simpl.
      by rewrite get_val_err.
  Qed.
  #[global] Instance PairLSCtx_hom β `{!AsVal β} : IT_hom (PairLSCtx β).
  Proof.
    unfold PairLSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intros a. by apply pairT_tick_l.
    - intros op i k. cbn-[pairIT]. rewrite pairT_vis_l.
      repeat f_equiv. intro. reflexivity.
    - intros e. simpl.
      rewrite get_val_ITV/=.
      by rewrite get_val_err.
  Qed.

End pairs.
