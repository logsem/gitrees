(** Encoding of pairs *)
(* From Equations Require Import Equations. *)
(* From iris.proofmode Require Import classes tactics. *)
From gitrees Require Import prelude.
From gitrees.gitree Require Import core lambda.

Section pairs.
  Variable (E : opsInterp).
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Program Definition pairTV : IT -n> IT -n> IT := λne a b,
      Fun (Next $ λne f, APP' (APP' f a) b).
  Solve Obligations with repeat (repeat intro; simpl; repeat f_equiv); solve_proper.
  Program Definition pairT : IT -n> IT -n> IT := λne a b,
      get_val (λne v2, get_val (λne v1, pairTV v1 v2) a) b.
  Solve Obligations with repeat (repeat intro; simpl; repeat f_equiv); solve_proper.

  Program Definition proj1Tf : IT := (Fun $ Next (λne a, Fun $ Next $ λne b, a)).
  Solve Obligations with repeat (repeat intro; simpl; repeat f_equiv); solve_proper.
  Program Definition proj1T : IT -n> IT := λne t, APP' t proj1Tf.

  Program Definition projT2f : IT := (Fun $ Next (λne a, Fun $ Next $ λne b, b)).
  Program Definition proj2T : IT -n> IT := λne t, APP' t projT2f.

  Lemma pairT_tick_l α β : pairT α (Tick β) ≡ Tick $ pairT α β.
  Proof. unfold pairT. rewrite get_val_tick//. Qed.
  Lemma pairT_tick_r α β `{!AsVal β} :
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
    rewrite APP'_Fun. rewrite APP_Fun.
    simpl. rewrite -Tick_eq. f_equiv.
    set (f :=  Fun (Next (λne _ : IT, α))).
    trans (APP (Tick f) (Next β)).
    { rewrite APP_APP'_ITV.
      f_equiv. f_equiv.
      rewrite APP_APP'_ITV.
      rewrite APP_Fun.
      rewrite -Tick_eq. f_equiv.
      simpl. unfold f. f_equiv.
      intro. simpl. reflexivity. }
    rewrite /f. rewrite APP_Tick.
    f_equiv. rewrite APP_Fun.
    rewrite -Tick_eq/=//.
  Qed.

  Lemma proj2T_pair α β `{!AsVal α, !AsVal β} : proj2T (pairT α β) ≡ Tick_n 3 β.
  Proof.
    cbn-[pairTV].
    simpl.
    trans (APP' (pairTV α β) projT2f).
    { do 2 f_equiv. rewrite get_val_ITV/=.
      rewrite get_val_ITV/=. done. }
    rewrite APP'_Fun. rewrite APP_Fun.
    simpl. rewrite -Tick_eq. f_equiv.
    rewrite APP_APP'_ITV.
    etrans.
    { apply APP_Proper. rewrite APP_APP'_ITV.
      rewrite APP_Fun. simpl. rewrite -Tick_eq. reflexivity. }
    rewrite APP_Tick. f_equiv.
    rewrite APP_Fun/=. by rewrite Tick_eq.
  Qed.

End pairs.

