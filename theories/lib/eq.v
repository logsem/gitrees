From gitrees Require Import prelude.
From gitrees Require Import gitree.
From iris.algebra Require Import list.

Section ofe_decision.
  Class Ofe_decide_eq (R : ofe) :=
    MkOfeDecide {
        ofe_decision : R -n> R -n> boolO;
        ofe_decision_reflect : ∀ a b, ofe_decision a b = true -> a ≡ b;
      }.
  Arguments MkOfeDecide {_}.

  Global Program Instance ofe_decide_eq_nat : Ofe_decide_eq natO
    := MkOfeDecide (λne x y, Nat.eqb x y) _.
  Next Obligation.
    intros; simpl in *.
    rewrite Nat.eqb_eq in H.
    done.
  Qed.
  Fail Next Obligation.

  Global Program Instance ofe_decide_eq_unit : Ofe_decide_eq unitO
    := MkOfeDecide (λne x y, true) _.
  Next Obligation.
    intros a b; simpl in *.
    by destruct a, b.
  Qed.
  Fail Next Obligation.

  Global Program Instance ofe_decide_eq_bool : Ofe_decide_eq boolO
    := MkOfeDecide (λne x y, Bool.eqb x y) _.
  Next Obligation.
    intros; simpl in *.
    by apply eqb_prop in H.
  Qed.
  Fail Next Obligation.

  Global Instance forallb_ne {A : ofe} n :
    Proper ((dist n) ==> (dist n) ==> dist n) (λ f : A -n> boolO, @forallb A f).
  Proof.
    intros x y Hxy a.
    induction a as [| a1 a2 IH].
    - intros [| b1 b2] Hab; first done.
      inversion Hab.
    - intros [| b1 b2] Hab; first inversion Hab.
      simpl.
      f_equiv.
      + inversion Hab; subst.
        rewrite (Hxy a1).
        by f_equiv.
      + inversion Hab; subst.
        apply IH.
        done.
  Qed.

  Global Program Instance ofe_decide_eq_list `{!Ofe_decide_eq R} : Ofe_decide_eq (listO R)
    := MkOfeDecide
         (λne x y, Nat.eqb (length x) (length y)
                   && forallb (λne x, ofe_decision (fstO x) (snd x)) (zip_with (λ a b, (a, b)) x y))
         _.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    intros R ? x n l l' Hl.
    f_equiv.
    {
      f_equiv.
      by apply List.Forall2_length in Hl.
    }
    apply forallb_ne; last solve_proper.
    intros [? ?]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros R ? n l l' Hl y; simpl.
    f_equiv.
    - f_equiv.
      by apply List.Forall2_length in Hl.
    - unshelve epose proof
        (@forallb_ne (prodO R R) n (λne x : prodO R R, ofe_decision x.1 x.2)
           (λne x : prodO R R, ofe_decision x.1 x.2) (reflexivity _));
        [apply _ | solve_proper |].
      simpl in H.
      apply H.
      solve_proper.
  Qed.
  Next Obligation.
    intros R ? a; simpl in *.
    induction a as [| a1 a2 IH].
    - intros [| b1 b2]; first done.
      inversion 1.
    - intros [| b1 b2]; first inversion 1.
      rewrite andb_true_iff.
      intros [H1 H2].
      simpl in H1.
      simpl in H2.
      rewrite andb_true_iff in H2.
      destruct H2 as [H2 H3].
      apply ofe_decision_reflect in H2.
      rewrite H2.
      f_equiv.
      apply IH.
      apply andb_true_iff.
      rewrite H1 H3.
      done.
  Qed.
  Fail Next Obligation.

  Global Program Instance ofe_decide_eq_sum {A B : ofe}
    {H1 : Ofe_decide_eq A}
    {H2 : Ofe_decide_eq B}
    : Ofe_decide_eq (sumO A B)
    := MkOfeDecide
         (λne x y, match x with
                   | inl x' =>
                       match y with
                       | inl y' => ofe_decision x' y'
                       | inr _ => false
                       end
                   | inr x' =>
                       match y with
                       | inl _ => false
                       | inr y' => ofe_decision x' y'
                       end
                   end) _.
  Next Obligation.
    intros A B ?? [x1 | x2] n [y1 | y2] [z1 | z2] H; simpl;
      inversion H; subst; solve_proper.
  Qed.
  Next Obligation.
    intros A B ?? n [x1 | x2] [y1 | y2] H; simpl;
      inversion H; subst; intros [z1 | z2]; simpl;
      solve_proper.
  Qed.
  Next Obligation.
    intros A B ?? [x1 | x2] [y1 | y2] H; simpl in *.
    - f_equiv.
      by apply ofe_decision_reflect.
    - by exfalso.
    - by exfalso.
    - f_equiv.
      by apply ofe_decision_reflect.
  Qed.
  Fail Next Obligation.

End ofe_decision.

Arguments MkOfeDecide {_}.

Section decidable_equality.
  Context {A} `{AC : !Cofe A}.
  Context {E : opsInterp}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Context `{!invGS_gen hlc Σ}.
  Notation iProp := (iProp Σ).

  Context `{SO : !SubOfe natO A}.
  Context {dec : Ofe_decide_eq A}.

  Program Definition safe_compare_def
    : IT -> IT -> IT := λ a b,
      (get_val
         (λne v2,
           get_val
             (λne v1,
               get_ret2 (λne x y, Ret (if (ofe_decision x y) then 1 else 0)) v2 v1)
             b) a).
  Next Obligation.
    intros ????? n.
    intros ?? H.
    f_equiv.
    by rewrite H.
  Qed.
  Next Obligation.
    intros ???? n.
    intros x y H z; simpl.
    f_equiv.
    assert (ofe_decision x z ≡{n}≡ ofe_decision y z) as ->; first solve_proper.
    done.
  Qed.
  Next Obligation.
    intros ??? n.
    intros ?? H.
    by f_equiv.
  Qed.
  Next Obligation.
    intros ?? n.
    intros ?? H.
    do 2 f_equiv; simpl.
    intros ?; simpl.
    by f_equiv.
  Qed.

  Global Instance safe_compare_ne' n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) safe_compare_def.
  Proof.
    intros a1 a2 Ha b1 b2 Hb.
    solve_proper_prepare.
    f_equiv; last done.
    f_equiv; intros ?; simpl.
    by f_equiv.
  Qed.
  Global Instance safe_compare_proper' :
    Proper ((≡) ==> (≡) ==> (≡)) safe_compare_def.
  Proof.
    intros a1 a2 Ha b1 b2 Hb.
    solve_proper_prepare.
    f_equiv; last done.
    f_equiv; intros ?; simpl.
    by f_equiv.
  Qed.

  Program Definition safe_compare
    : IT -n> IT -n> IT := λne a b, safe_compare_def a b.
  Solve All Obligations with solve_proper.

  Lemma safe_compare_reflect x y : safe_compare x y ≡ Ret 1 → x ≡ y.
  Proof using A AC SO dec Σ.
    destruct (IT_dont_confuse x)
      as [[e Ha] | [[m Ha] | [ [g Ha] | [[α' Ha]|[op [i [ko Ha]]]] ]]].
    - intros H.
      rewrite /safe_compare /= Ha in H.
      rewrite /safe_compare_def get_val_err in H.
      exfalso.
      symmetry in H.
      assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
      iApply IT_ret_err_ne.
      rewrite <-H.
      done.
    - intros H.
      rewrite /safe_compare /= Ha in H.
      rewrite /safe_compare_def in H.
      destruct (IT_dont_confuse y)
        as [[e' Ha'] | [[m' Ha'] | [ [g' Ha'] | [[α'' Ha']|[op' [i' [ko' Ha']]]] ]]].
      + rewrite core.get_val_ret /= in H.
        rewrite Ha' in H.
        rewrite get_val_err in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_err_ne.
        rewrite ->H.
        done.
      + rewrite core.get_val_ret /= in H.
        rewrite Ha' in H.
        rewrite core.get_val_ret /= in H.
        rewrite core.get_ret_ret /= in H.
        rewrite core.get_ret_ret /= in H.
        destruct (ofe_decision m m') eqn:Heq.
        * apply ofe_decision_reflect in Heq.
          rewrite Heq in Ha.
          by rewrite -Ha' in Ha.
        * exfalso.
          assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
          iAssert (0 ≡ 1)%I as "%G".
          {
            iApply Ret_inj.
            rewrite <-H.
            done.
          }
          inversion G.
      + rewrite core.get_val_ret /= in H.
        rewrite Ha' in H.
        rewrite get_val_fun /= in H.
        rewrite core.get_ret_ret /= in H.
        rewrite get_ret_fun /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_err_ne.
        rewrite ->H.
        done.
      + rewrite core.get_val_ret /= in H.
        rewrite Ha' in H.
        rewrite get_val_tick /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_tick_ne.
        rewrite ->H.
        done.
      + rewrite core.get_val_ret /= in H.
        rewrite Ha' in H.
        rewrite get_val_vis /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_vis_ne.
        rewrite ->H.
        done.
    - intros H.
      rewrite /safe_compare /= /safe_compare_def /= Ha get_val_fun /= in H.
      destruct (IT_dont_confuse y)
        as [[e' Ha'] | [[m' Ha'] | [ [g' Ha'] | [[α'' Ha']|[op' [i' [ko' Ha']]]] ]]].
      + rewrite Ha' get_val_err in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_err_ne.
        rewrite ->H.
        done.
      + rewrite Ha' core.get_val_ret /= in H.
        rewrite get_ret_fun in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_err_ne.
        rewrite ->H.
        done.
      + rewrite Ha' get_val_fun /= in H.
        rewrite get_ret_fun in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_err_ne.
        rewrite ->H.
        done.
      + rewrite Ha' get_val_tick /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_tick_ne.
        rewrite ->H.
        done.
      + rewrite Ha' in H.
        rewrite get_val_vis /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iApply IT_ret_vis_ne.
        rewrite ->H.
        done.
    - intros H.
      rewrite /safe_compare /= /safe_compare_def /= Ha get_val_tick /= in H.
      exfalso.
      assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
      iApply IT_ret_tick_ne.
      rewrite ->H.
      done.
    - intros H.
      rewrite /safe_compare /= /safe_compare_def /= Ha get_val_vis /= in H.
      exfalso.
      assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
      iApply IT_ret_vis_ne.
      rewrite ->H.
      done.
  Qed.

  Lemma safe_compare_ret x y : safe_compare (Ret x) (Ret y) ≡ Ret (if ofe_decision x y then 1 else 0).
  Proof.
    rewrite /safe_compare /= /safe_compare_def.
    rewrite get_val_ret /= get_val_ret /= get_ret_ret /= get_ret_ret //=.
  Qed.

  Lemma safe_compare_tick_l x y : safe_compare (Tick x) y ≡ Tick (safe_compare x y).
  Proof.
    rewrite /safe_compare /= /safe_compare_def.
    rewrite get_val_tick.
    f_equiv.
  Qed.

  Lemma safe_compare_tick_r x `{!AsVal x} y : safe_compare x (Tick y) ≡ Tick (safe_compare x y).
  Proof.
    rewrite /safe_compare /= /safe_compare_def.
    rewrite get_val_ITV /=.
    rewrite get_val_tick.
    f_equiv.
    rewrite get_val_ITV /=.
    f_equiv.
  Qed.

End decidable_equality.

Arguments safe_compare {_ _ _ _ _}.
