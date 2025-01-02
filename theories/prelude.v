(** Useful theorems/functions on OFEs and other stuff missing from Iris *)
From stdpp Require Import nat_cancel.
From iris.prelude Require Export options prelude.
From iris.algebra Require Import list ofe local_updates.
From iris.bi Require Import notation.
From iris.si_logic Require Import bi siprop.
From iris.proofmode Require Import classes tactics modality_instances
                                   coq_tactics reduction.

Definition sum_map' {A B C : Set} (f : A → C) (g : B → C) : sum A B → C :=
  λ x, match x with | inl x' => f x' | inr x' => g x' end.

Program Definition idfun {A : ofe} : A -n> A := λne x, x.

(** OFEs stuff *)
Notation "F ♯ E" := (oFunctor_apply F E) (at level 20, right associativity).

Lemma ccompose_id_l {A B : ofe} (f : A -n> B) :
  cid ◎ f ≡ f.
Proof.
  intros x; reflexivity.
Qed.

Lemma ccompose_id_r {A B : ofe} (f : A -n> B) :
  f ◎ cid ≡ f.
Proof.
  intros x; reflexivity.
Qed.

Infix "≃" := (ofe_iso) (at level 50).

Definition ofe_iso_1' {A B : ofe} (p : A ≃ B) : A → B := ofe_iso_1 p.
Coercion ofe_iso_1' : ofe_iso >-> Funclass.
Notation "f ^-1" := (ofe_iso_2 f) (at level 20) : function_scope.

#[export] Instance optionO_map_proper (A B : ofe) :
  Proper ((≡) ==> (≡)) (@optionO_map A B).
Proof. solve_proper. Qed.

#[export] Instance prodO_map_proper (A B C D : ofe) :
  Proper ((≡) ==> (≡) ==> (≡)) (@prodO_map A B C D).
Proof.
  intros ?? H ?? G [a b]; simpl.
  f_equiv; solve_proper.
Qed.

Program Definition flipO {A B C : ofe} : (A -n> B -n> C) -n> B -n> A -n> C
  := λne f x y, f y x.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.

Program Definition later_ap {A B} (f : later (A -n> B)) : laterO A -n> laterO B :=
  λne x, Next $ (later_car f) (later_car x).
#[export] Instance later_ap_ne {A B} : NonExpansive (@later_ap A B).
Proof.
  intros n f g Hfg. intros x. simpl.
  eapply Next_contractive. destruct n; eauto using dist_later_0, dist_later_S.
  apply dist_later_S. f_equiv. eapply later_car_anti_contractive; eauto.
Qed.
Definition laterO_ap {A B} := OfeMor (@later_ap A B).

Program Definition sumO_rec {A B C : ofe} (f : A -n> C) (g : B -n> C) : sumO A B -n> C :=
  λne x, match x with
         | inl a => f a
         | inr b => g b
         end.
Next Obligation.
  intros. intros x y Hxy. simpl.
  destruct x as [a1|b1], y as [a2|b2]; try by inversion Hxy.
  - apply inl_ne_inj in Hxy. by f_equiv.
  - apply inr_ne_inj in Hxy. by f_equiv.
Qed.

#[export] Instance sumO_rec_ne n A B C : Proper (dist n ==> dist n ==> dist n) (@sumO_rec A B C).
Proof.
  intros f1 f2 Hf g1 g2 Hg. intros [x|y]; simpl; eauto.
Qed.

#[export] Instance sumO_rec_proper A B C : Proper ((≡) ==> (≡) ==> (≡)) (@sumO_rec A B C).
Proof.
  intros f1 f2 Hf g1 g2 Hg. intros [x|y]; simpl; eauto.
Qed.

Program Definition Empty_setO_rec A : Empty_setO -n> A := λne x, Empty_set_rect (λ _, A) x.
Next Obligation. intros A n x y. inversion x. Qed.

Program Definition constO {A B : ofe} : A -n> B -n> A := λne x _, x.
Next Obligation. solve_proper. Qed.
Next Obligation. solve_proper. Qed.


Lemma laterO_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
  laterO_map (g ◎ f) x ≡ laterO_map g (laterO_map f x).
Proof. by destruct x. Qed.
Lemma laterO_map_id {A} (x : laterO A) : laterO_map idfun x ≡ x.
Proof. by destruct x. Qed.
Lemma laterO_map_Next {A B} (f : A -n> B) (x : A) : laterO_map f (Next x) ≡ Next (f x).
Proof. reflexivity. Qed.

Program Definition inlO {A B : ofe} : A -n> sumO A B := λne x, inl x.
Program Definition inrO {A B : ofe} : B -n> sumO A B := λne x, inr x.
Program Definition fstO {A B : ofe} : prodO A B -n> A := λne x, fst x.
Program Definition sndO {A B : ofe} : prodO A B -n> B := λne x, snd x.
Program Definition prod_in {A B C : ofe} : (C -n> A) -n> (C -n> B) -n> C -n> prodO A B
    := λne f g x, (f x, g x).
Solve Obligations with solve_proper.

Definition sumO_assoc A B C : sumO A (sumO B C) ≃ sumO (sumO A B) C.
Proof.
  simple refine (OfeIso _ _ _ _).
  - refine (sumO_rec (inlO ◎ inlO) _).
    refine (sumO_rec (inlO ◎ inrO) inrO).
  - refine (sumO_rec _ (inrO ◎ inrO)).
    refine (sumO_rec inlO (inrO ◎ inlO)).
  - intros [[?|?]|?]; simpl; eauto.
  - intros [?|[?|?]]; simpl; eauto.
Defined.
Definition sumO_compat_l A B C : A ≃ B → sumO A C ≃ sumO B C.
Proof.
  intros f.
  simple refine (OfeIso _ _ _ _).
  - refine (sumO_rec (inlO ◎ f) inrO).
  - refine (sumO_rec (inlO ◎ f^-1) inrO).
  - intros [?|?]; simpl; eauto.
    rewrite ofe_iso_12//.
  - intros [?|?]; simpl; eauto.
    rewrite ofe_iso_21//.
Defined.
Definition sumO_sym A B : sumO A B ≃ sumO B A.
Proof.
  simple refine (OfeIso _ _ _ _).
  - refine (sumO_rec inrO inlO).
  - refine (sumO_rec inrO inlO).
  - intros [?|?]; simpl; eauto.
  - intros [?|?]; simpl; eauto.
Defined.
Definition sumO_unitO_r A : sumO A Empty_setO ≃ A.
Proof.
  simple refine (OfeIso _ inlO _ _).
  - refine (sumO_rec cid (Empty_setO_rec _)).
  - simpl. eauto.
  - intros [?|?]; simpl; eauto. inversion o.
Defined.

Program Definition NextO {A} : A -n> laterO A := λne x, Next x.

Definition mmuu `{!Cofe A, !Inhabited A} (f : laterO A -n> A) : A.
Proof.
  refine (fixpoint (f ◎ NextO)).
  solve_contractive.
Defined.

Lemma mmuu_unfold {A} `{!Cofe A, Inhabited A} (f : laterO A -n> A) :
  mmuu f ≡ f (Next $ mmuu f).
Proof.
  rewrite /mmuu.
  etrans.
  { eapply (fixpoint_unfold (A:=A)). }
  simpl. f_equiv.
Qed.

Global Instance mmuu_ne {A} `{!Cofe A, Inhabited A} :
  NonExpansive (@mmuu A _ _).
Proof.
  repeat intro. unfold mmuu.
  apply fixpoint_ne. intros z.
  solve_proper.
Qed.

Section siProp.
Import siprop.
Import siProp_primitive.
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_pure, bi_entails, bi_later,
    bi_and, bi_or, bi_impl, bi_forall, bi_exist,
    bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  unfold internal_eq, bi_internal_eq_internal_eq,
    plainly, bi_plainly_plainly; simpl;
  siProp_primitive.unseal.
Lemma internal_eq_pointwise {A B : ofe} (f g : A -n> B) :
  ⊢@{bi.siPropI} (∀ x, f x ≡ g x) → f ≡ g.
Proof.
  unseal. split. intros n _ m Hnm H x. apply H.
Qed.
End siProp.

(** "Beefed up" version of iRewrite.
See also : https://gitlab.mpi-sws.org/iris/iris/-/issues/519
 *)
Local Ltac iClearHyp H :=
  eapply tac_clear with H _ _; (* (i:=H) *)
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iClear:" H "not found"
    |pm_reduce; tc_solve ||
     let H := pretty_ident H in
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iClear:" H ":" P "not affine and the goal not absorbing"
    |pm_reduce].

Local Ltac iRewriteFindPred :=
  match goal with
  | |- _ ⊣⊢ ?Φ ?x =>
     generalize x;
     match goal with |- (∀ y, @?Ψ y ⊣⊢ _) => unify Φ Ψ; reflexivity end
  end.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite _ Heq _ _ lr);
      [pm_reflexivity ||
       let Heq := pretty_ident Heq in
       fail "iRewrite:" Heq "not found"
      |tc_solve ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      | solve [ intros ??? ->; reflexivity | solve_proper ] (** THIS IS CHANGED *)
      |pm_prettify; iClearHyp Heq]).

Tactic Notation "iRewrite" open_constr(lem) := iRewriteCore Right lem.
Tactic Notation "iRewrite" "-" open_constr(lem) := iRewriteCore Left lem.

Local Tactic Notation "iRewriteCore" constr(lr) open_constr(lem) "in" constr(H) :=
  iPoseProofCore lem as true (fun Heq =>
    eapply (tac_rewrite_in _ Heq _ _ H _ _ lr);
      [pm_reflexivity ||
       let Heq := pretty_ident Heq in
       fail "iRewrite:" Heq "not found"
      |pm_reflexivity ||
       let H := pretty_ident H in
       fail "iRewrite:" H "not found"
      |tc_solve ||
       let P := match goal with |- IntoInternalEq ?P _ _ ⊢ _ => P end in
       fail "iRewrite:" P "not an equality"
      |iRewriteFindPred
      | solve [ intros ??? ->; reflexivity | solve_proper ] (** THIS IS CHANGED *)
      |pm_reduce; pm_prettify; iClearHyp Heq]).

Tactic Notation "iRewrite" open_constr(lem) "in" constr(H) :=
  iRewriteCore Right lem in H.
Tactic Notation "iRewrite" "-" open_constr(lem) "in" constr(H) :=
  iRewriteCore Left lem in H.

(** Beefed up solve_proper *)
Ltac solve_proper_please := repeat (repeat intro; simpl; repeat f_equiv); solve_proper.
