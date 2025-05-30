From gitrees Require Import prelude.
From gitrees Require Import gitree.
From iris.algebra Require Import list.

Section ofe_decision.
  Class Ofe_decide_eq (R : ofe) :=
    MkOfeDecide {
        ofe_decision : R -n> R -n> boolO;
        ofe_decision_reflect : ∀ a b, ofe_decision a b = true -> a ≡ b;
        ofe_decision_reify_true : ∀ a b, a ≡ b -> ofe_decision a b = true;
        ofe_decision_reify_false : ∀ a b, (~ (a ≡ b)) -> ofe_decision a b = false;
      }.
  Arguments MkOfeDecide {_}.

  Global Program Instance ofe_decide_eq_nat : Ofe_decide_eq natO
    := MkOfeDecide (λne x y, Nat.eqb x y) _ _ _.
  Next Obligation.
    intros; simpl in *.
    rewrite Nat.eqb_eq in H.
    done.
  Qed.
  Next Obligation.
    intros ?? ->.
    by rewrite Nat.eqb_eq.
  Qed.
  Next Obligation.
    intros ?? H.
    by rewrite Nat.eqb_neq.
  Qed.
  Fail Next Obligation.

  Global Program Instance ofe_decide_eq_Z : Ofe_decide_eq ZO
    := MkOfeDecide (λne x y, Z.eqb x y) _ _ _.
  Next Obligation.
    intros; simpl in *.
    rewrite Z.eqb_eq in H.
    done.
  Qed.
  Next Obligation.
    intros ?? ->.
    by rewrite Z.eqb_eq.
  Qed.
  Next Obligation.
    intros ?? H.
    by rewrite Z.eqb_neq.
  Qed.
  Fail Next Obligation.

  Global Program Instance ofe_decide_eq_unit : Ofe_decide_eq unitO
    := MkOfeDecide (λne x y, true) _ _ _.
  Next Obligation.
    intros a b; simpl in *.
    by destruct a, b.
  Qed.
  Next Obligation.
    intros [] [] _.
    done.
  Qed.
  Next Obligation.
    intros [] [] H.
    exfalso.
    by apply H.
  Qed.
  Fail Next Obligation.

  Global Program Instance ofe_decide_eq_bool : Ofe_decide_eq boolO
    := MkOfeDecide (λne x y, Bool.eqb x y) _ _ _.
  Next Obligation.
    intros; simpl in *.
    by apply eqb_prop in H.
  Qed.
  Next Obligation.
    intros ?? ->; simpl.
    apply eqb_reflx.
  Qed.
  Next Obligation.
    intros ?? H.
    by rewrite eqb_false_iff.
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
                   end) _ _ _.
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
  Next Obligation.
    intros ???? [|] [|] H; simpl in *.
    - apply ofe_decision_reify_true.
      by inversion H; subst.
    - by inversion H.
    - by inversion H.
    - apply ofe_decision_reify_true.
      by inversion H; subst.
  Qed.
  Next Obligation.
    intros ???? [|] [|] H; simpl in *.
    - apply ofe_decision_reify_false.
      intros G. by rewrite G in H.
    - done.
    - done.
    - apply ofe_decision_reify_false.
      intros G. by rewrite G in H.
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

  Context `{SO : !SubOfe boolO A}.
  Context {dec : Ofe_decide_eq A}.

  Definition get_unboxed_ret (f : A -n> IT)
    : IT -n> IT
    := IT_rec1 IT
         Err (* error *)
         f (* nat *)
         (constO (Ret false)) (* function *)
         (Tau ◎ Iter_Tau _) (* step *)
         Vis_
         IT_unfold.
  
  Global Instance get_unboxed_ret_ne : NonExpansive get_unboxed_ret.
  Proof.
    repeat intro. unfold get_unboxed_ret.
    apply IT_rec1_ne; solve_proper.
  Qed.
  Global Instance get_unboxed_ret_proper : Proper ((≡) ==> (≡)) get_unboxed_ret.
  Proof.
    repeat intro. unfold get_unboxed_ret.
    apply IT_rec1_proper; solve_proper.
  Qed.

  Program Definition get_unboxed_ret2 (f : A -n> A -n> IT)
    : IT -n> IT -n> IT := λne x y,
      get_unboxed_ret
        (λne x, get_unboxed_ret (λne y, f x y) y) x.
  Solve All Obligations with solve_proper_please.
  
  Global Instance get_unboxed_ret2_ne : NonExpansive get_unboxed_ret2.
  Proof.
    intros n f1 f2 Hf. unfold get_unboxed_ret2.
    intros x y. simpl. apply get_unboxed_ret_ne. 
    clear x. intros x. simpl. apply get_unboxed_ret_ne.
    clear y. intros y. simpl. apply Hf.
  Qed.
  
  Global Instance get_unboxed_ret2_proper :
    Proper ((≡) ==> (≡)) get_unboxed_ret2.
  Proof.
    apply ne_proper. apply get_unboxed_ret2_ne.
  Qed.

  Lemma get_unboxed_ret_err f e : get_unboxed_ret f (Err e) ≡ Err e.
  Proof. by rewrite IT_rec1_err. Qed.
  Lemma get_unboxed_ret_fun f g : get_unboxed_ret f (Fun g) ≡ Ret false.
  Proof. by rewrite IT_rec1_fun. Qed.
  Lemma get_unboxed_ret_ret f n : get_unboxed_ret f (Ret n) ≡ f n.
  Proof. by rewrite IT_rec1_ret. Qed.
  Lemma get_unboxed_ret_tick f t : get_unboxed_ret f (Tick t) ≡ Tick (get_unboxed_ret f t).
  Proof.
    Opaque Tau.
    rewrite IT_rec1_tau.
    cbn-[prod_in].
    rewrite Tick_eq.
    f_equiv.
    rewrite later_map_Next /=.
    done.
  Qed.
  Lemma get_unboxed_ret_tick_n f n t : get_unboxed_ret f (Tick_n n t) ≡ Tick_n n (get_unboxed_ret f t).
  Proof.
    induction n; first reflexivity.
    rewrite get_unboxed_ret_tick. by rewrite IHn.
  Qed.
  Lemma get_unboxed_ret_vis f op i k : get_unboxed_ret f (Vis op i k)
                                         ≡ Vis op i (laterO_map (get_unboxed_ret f) ◎ k).
  Proof.
    rewrite IT_rec1_vis. cbn-[prod_in]. f_equiv.
    - rewrite -oFunctor_map_compose.
      etrans. 2:{ eapply oFunctor_map_id. }
      repeat f_equiv.
      + intro x. reflexivity.
      + intro x. reflexivity.
    - intros x. cbn-[prod_in].
      rewrite -later_map_compose.
      f_equiv.
      rewrite -oFunctor_map_compose.
      f_equiv.
      simpl.
      etrans.
      2: { eapply oFunctor_map_id. }
      repeat f_equiv.
      * intros ?; done.
      * intros y. simpl. done.      
  Qed.

  Program Definition safe_compare_def
    : IT -> IT -> IT := λ a b,
      (get_val
         (λne v2,
           get_val
             (λne v1,
               get_unboxed_ret2 (λne x y, Ret (ofe_decision x y)) v2 v1)
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

  Lemma safe_compare_reflect x y : safe_compare x y ≡ Ret true → x ≡ y.
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
        rewrite get_unboxed_ret_ret /= in H.
        rewrite get_unboxed_ret_ret /= in H.
        destruct (ofe_decision m m') eqn:Heq.
        * apply ofe_decision_reflect in Heq.
          rewrite Heq in Ha.
          by rewrite -Ha' in Ha.
        * exfalso.
          assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
          iAssert (false ≡ true)%I as "%G".
          {
            iApply Ret_inj.
            rewrite <-H.
            done.
          }
          inversion G.
      + rewrite core.get_val_ret /= in H.
        rewrite Ha' in H.
        rewrite get_val_fun /= in H.
        rewrite get_unboxed_ret_ret /= in H.
        rewrite get_unboxed_ret_fun /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iDestruct (Ret_inj with "[]") as "H".
        { iPureIntro. apply H. }
        iDestruct "H" as "%G".
        Unshelve.
        2: apply _.
        inversion G.
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
        rewrite get_unboxed_ret_fun /= in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iDestruct (Ret_inj with "[]") as "H".
        { iPureIntro. apply H. }
        iDestruct "H" as "%G".
        Unshelve.
        2: apply _.
        inversion G.        
      + rewrite Ha' get_val_fun /= in H.
        rewrite get_unboxed_ret_fun in H.
        exfalso.
        assert (⊢@{iProp} False)%I; last by eapply uPred.pure_soundness.
        iDestruct (Ret_inj with "[]") as "H".
        { iPureIntro. apply H. }
        iDestruct "H" as "%G".
        Unshelve.
        2: apply _.
        inversion G.
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

  Lemma safe_compare_ret x y : safe_compare (Ret x) (Ret y) ≡ Ret (ofe_decision x y).
  Proof.
    rewrite /safe_compare /= /safe_compare_def.
    rewrite get_val_ret /= get_val_ret /= get_unboxed_ret_ret /= get_unboxed_ret_ret //=.
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
