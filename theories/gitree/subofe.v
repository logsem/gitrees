(* SubOfe: a typeclass for working with generalized return type "a la carte" *)
From iris.prelude Require Import options.
From gitrees Require Import prelude gitree.core.

Class SubOfe (A B : ofe) :=
  { subOfe_rest : ofe;
    subOfe_in : ofe_iso (sumO A subOfe_rest) B }.

#[global] Instance subOfe_id A : SubOfe A A.
Proof.
  refine ({| subOfe_rest := Empty_setO |}).
  apply sumO_unitO_r.
Defined.
#[global] Instance subOfe_inl A B C `{!SubOfe A B} : SubOfe A (sumO B C).
Proof.
  refine ({| subOfe_rest := sumO subOfe_rest C |}).
  eapply iso_ofe_trans.
  { apply sumO_assoc. }
  apply sumO_compat_l. apply subOfe_in.
Defined.
#[global] Instance subOfe_inr A B C `{!SubOfe A B} : SubOfe A (sumO C B).
Proof.
  refine ({| subOfe_rest := sumO subOfe_rest C |}).
  eapply iso_ofe_trans.
  { apply sumO_assoc. }
  eapply iso_ofe_trans.
  { apply sumO_compat_l. apply subOfe_in. }
  apply sumO_sym.
Defined.
#[global] Hint Mode SubOfe ! ! : typeclass_instances.

Section it_subofe.
  Context {E : opsInterp}.
  Context {A B : ofe} `{!Cofe A, !Cofe B} `{!SubOfe A B}.
  Notation IT := (IT E B).

  Definition Ret : A -n> IT := Ret ◎ subOfe_in ◎ inlO.
  Program Definition RetV : A -n> ITV E B := OfeMor RetV ◎ subOfe_in ◎ inlO.
  Definition get_ret (f : A -n> IT) : IT -n> IT := get_ret (sumO_rec f Err1 ◎ subOfe_in^-1).

  #[global] Instance get_ret_ne n : Proper ((dist n) ==> (dist n)) get_ret.
  Proof.
    repeat intro. unfold get_ret. solve_proper.
  Qed.
  #[global] Instance get_ret_proper : Proper ((≡) ==> (≡)) get_ret.
  Proof.
    repeat intro. unfold get_ret. solve_proper.
  Qed.

  Program Definition get_ret2 (f : A -n> A -n> IT) : IT -n> IT -n> IT := λne x y,
      get_ret (λne x, get_ret (λne y, f x y) y) x.
  Solve All Obligations with solve_proper_please.
  Global Instance get_ret2_ne n : Proper ((dist n) ==> (dist n)) get_ret2.
  Proof.
    intros f1 f2 Hf. unfold get_ret2.
    intros x y. simpl. apply get_ret_ne.
    clear x. intros x. simpl. apply get_ret_ne.
    clear y. intros y. simpl. apply Hf.
  Qed.
  Global Instance get_ret2_proper : Proper ((≡) ==> (≡)) get_ret2.
  Proof.
    intros f1 f2 Hf. unfold get_ret2.
    intros x y. simpl. apply get_ret_proper.
    clear x. intros x. simpl. apply get_ret_proper.
    clear y. intros y. simpl. apply Hf.
  Qed.

  Lemma get_ret_ret f n : get_ret f (Ret n) ≡ f n.
  Proof.
    rewrite get_ret_ret. cbn-[sumO_rec].
    rewrite ofe_iso_21. done.
  Qed.

  Lemma get_val_ret f n : get_val f (Ret n) ≡ f (Ret n).
  Proof. by rewrite IT_rec1_ret. Qed.
  Lemma get_fun_ret f n : get_fun f (Ret n) ≡ Err RuntimeErr.
  Proof. by rewrite IT_rec1_ret. Qed.

  Lemma IT_of_V_Ret n : IT_of_V (RetV n) ≡ Ret n.
  Proof. done. Qed.
  Lemma IT_to_V_Ret n : IT_to_V (Ret n) ≡ Some (RetV n).
  Proof. simpl. rewrite IT_to_V_Ret. done. Qed.

  #[export] Instance intoval_ret n : IntoVal (Ret n) (RetV n).
  Proof. unfold IntoVal. simpl. reflexivity. Qed.
  #[export] Instance asval_ret n : AsVal (Ret n).
  Proof. exists (RetV n). reflexivity. Qed.

  #[global] Opaque Ret RetV.
End it_subofe.
