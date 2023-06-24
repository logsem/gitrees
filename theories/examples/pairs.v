(** Encoding of pairs *)
From gitrees Require Import prelude.
From gitrees.gitree Require Import core lambda.

Section pairs.
  Context {E : opsInterp}.
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Program Definition pairTV : IT -n> IT -n> IT := λne a b,
      λit f, f ⊙ a ⊙ b.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Program Definition pairT : IT -n> IT -n> IT := λne a b,
      get_val (λne v2, get_val (λne v1, pairTV v1 v2) a) b.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

  Program Definition proj1Tf : IT := λit a b, a.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Program Definition proj1T : IT -n> IT := λne t, t ⊙ proj1Tf.

  Program Definition projT2f : IT := λit a b, b.
  Program Definition proj2T : IT -n> IT := λne t, t ⊙ projT2f.

  Lemma pairT_tick_r α β : pairT α (Tick β) ≡ Tick $ pairT α β.
  Proof. unfold pairT. rewrite get_val_tick//. Qed.
  Lemma pairT_tick_l α β `{!AsVal β} :
    pairT (Tick α) β ≡ Tick $ pairT α β.
  Proof. unfold pairT. rewrite !get_val_ITV /= get_val_tick//. Qed.
  Lemma pairT_vis_r α op i k :
    pairT α (Vis op i k) ≡ Vis op i (laterO_map (pairT α) ◎ k).
  Proof.
    unfold pairT. rewrite get_val_vis. f_equiv.
    intro x. simpl. done.
  Qed.
  Lemma pairT_vis_l β op i k `{!AsVal β} :
    pairT (Vis op i k) β ≡ Vis op i (laterO_map (flipO pairT β) ◎ k).
  Proof.
    unfold pairT. simpl. rewrite get_val_ITV/=.
    rewrite get_val_vis. f_equiv. f_equiv. f_equiv.
    intro x. simpl. rewrite get_val_ITV/=. done.
  Qed.

  Lemma proj1T_tick α : proj1T (Tick α) ≡ Tick $ proj1T α.
  Proof. simpl. by rewrite APP'_Tick_l. Qed.
  Lemma proj1T_vis op i k : proj1T (Vis op i k) ≡ Vis op i (laterO_map proj1T ◎ k).
  Proof.
    simpl. rewrite APP'_Vis_l.
    repeat f_equiv. intro x. simpl. reflexivity.
  Qed.
  Lemma proj2T_tick α : proj2T (Tick α) ≡ Tick $ proj2T α.
  Proof. simpl. by rewrite APP'_Tick_l. Qed.
  Lemma proj2T_vis op i k : proj2T (Vis op i k) ≡ Vis op i (laterO_map proj2T ◎ k).
  Proof.
    simpl. rewrite APP'_Vis_l.
    repeat f_equiv. intro x. simpl. reflexivity.
  Qed.

  Lemma proj1T_pair α β `{!AsVal α, !AsVal β} : proj1T (pairT α β) ≡ Tick_n 3 α.
  Proof.
    cbn-[pairTV].
    simpl.
    trans (APP' (pairTV α β) proj1Tf).
    { do 2 f_equiv. rewrite get_val_ITV/=.
      rewrite get_val_ITV/=. done. }
    rewrite APP'_Fun_l.
    simpl. rewrite -Tick_eq. f_equiv.
    set (f :=  λit _, α).
    trans (APP' (Tick f) β).
    { f_equiv. f_equiv.
      rewrite APP'_Fun_l/=.
      rewrite -Tick_eq. f_equiv.
      unfold f. f_equiv.
      intro. simpl. reflexivity. }
    rewrite /f. rewrite APP'_Tick_l.
    f_equiv. rewrite APP'_Fun_l/=.
    rewrite -Tick_eq/=//.
  Qed.

  Lemma proj2T_pair α β `{!AsVal α, !AsVal β} : proj2T (pairT α β) ≡ Tick_n 3 β.
  Proof.
    cbn-[pairTV].
    simpl.
    trans (APP' (pairTV α β) projT2f).
    { do 2 f_equiv. rewrite get_val_ITV/=.
      rewrite get_val_ITV/=. done. }
    rewrite APP'_Fun_l/= -Tick_eq.
    f_equiv.
    etrans.
    { apply APP'_Proper. rewrite APP'_Fun_l/=.
      rewrite -Tick_eq. reflexivity. }
    rewrite APP'_Tick_l. f_equiv.
    rewrite APP'_Fun_l/=. by rewrite Tick_eq.
  Qed.

  #[global] Instance proj1T_hom : IT_hom proj1T.
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intros a. apply proj1T_tick.
    - intros op i k. rewrite proj1T_vis.
      reflexivity.
    - intros e. simpl.
      by rewrite APP'_Err_l.
  Qed.
  #[global] Instance proj2T_hom : IT_hom proj2T.
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intros a. apply proj2T_tick.
    - intros op i k. rewrite proj2T_vis.
      reflexivity.
    - intros e. simpl.
      by rewrite APP'_Err_l.
  Qed.

  Definition PairRSCtx α : IT -n> IT := pairT α.
  Program Definition PairLSCtx β `{!AsVal β} : IT -n> IT := λne α, pairT α β.
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
    - intros op i k. cbn-[pairT]. rewrite pairT_vis_l.
      repeat f_equiv. intro. reflexivity.
    - intros e. simpl.
      rewrite get_val_ITV/=.
      by rewrite get_val_err.
  Qed.

End pairs.

