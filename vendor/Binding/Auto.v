Require Import Utf8.
Require Import Binding.Core.
Require Import Binding.Properties.
Require Import Binding.TermSimpl.

Local Open Scope bind_scope.

Ltac auto_map_id :=
  match goal with
  | |- ?f ≡ ı → fmap ?f ?t = ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_id with typeclass_instances)
              || (f_equal; now apply EQ))
  end.

Ltac auto_map_comp :=
  match goal with
  | |- ?f ∘ ?g ≡ ?h → fmap ?f (fmap ?g ?t) = fmap ?h ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_comp with typeclass_instances)
              || (f_equal; now apply EQ))
  end.

Ltac auto_map_bind_pure :=
  match goal with
  | |- ?f ̂ ≡ ?g → fmap ?f ?t = bind ?g ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_of with typeclass_instances)
              || now apply EQ)
  end.

Ltac auto_map_bind_comm :=
  match goal with
  | |- ?g₂ ∘ ?f₂ ̂ ≡ ?f₁ ̂ ∘ ?g₁ → bind ?g₂ (fmap ?f₂ ?t) = fmap ?f₁ (bind ?g₁ ?t) =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_comm with typeclass_instances)
              || rewrite map_to_bind; now apply EQ)
  end.

Ltac auto_bind_id :=
  match goal with
  | |- ?f ≡ ı → bind ?f ?t = ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_id with typeclass_instances)
              || now apply EQ)
  end.

Ltac auto_bind_comp :=
  match goal with
  | |- ?f ∘ ?g ≡ ?h → bind ?f (bind ?g ?t) = bind ?h ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_comp with typeclass_instances)
              || now apply EQ)
  end.

(*

Lemma ap_equal {A B : Type} (f g : A → B) (x y : A) :
  f = g → x = y → f x = g y.
Proof.
destruct 1; destruct 1; reflexivity.
Qed.

Local Ltac solve_equal :=
  reflexivity || (apply ap_equal; [ solve_equal | try reflexivity ]).

Local Open Scope bind_scope.

Local Ltac auto_map_id_arrow_eq Heq :=
  exact Heq || (apply Heq; fail) ||
  match goal with
  | |- (?f ↑) ≡ ı =>
    apply lift_id; auto_map_id_arrow_eq Heq
  | _ => idtac
  end.

Ltac auto_map_id :=
  let Heq := fresh "Heq" in
  intro Heq;
  match goal with
  | |- ?map _ _ ?f ?t = ?t =>
    destruct t; term_simpl; solve_equal; try (apply Heq; fail);
    match goal with
    | [ IH: ∀ (A : ?Obj) f (t : ?F A),
          f ≡ ı → ?map A A f t = t
      |- ?map _ _ _ ?t = ?t
      ] => apply IH; auto_map_id_arrow_eq Heq
    | |- ?fmap _ _ _ ?map _ _ _ _ ?t = ?t =>
      apply map_id; auto_map_id_arrow_eq Heq
    | |- ?map _ _ _ ?t = ?t =>
      apply map_id; auto_map_id_arrow_eq Heq
    | _ => idtac
    end
  end.

Local Ltac auto_map_map_comp_arrow_eq Heq :=
  exact Heq || (apply Heq; fail) ||
  match goal with
  | |- ?f ↑ ∘ ?g ↑ ≡ ?h ↑ =>
    apply lift_comp; auto_map_map_comp_arrow_eq Heq
  | _ => idtac
  end.

Ltac auto_map_map_comp :=
  let Heq := fresh "Heq" in
  intro Heq;
  match goal with
  | |- ?map _ _ ?f (?map _ _ ?g ?t) = ?map _ _ ?h ?t =>
    destruct t; term_simpl; solve_equal; try (apply Heq; fail);
    match goal with
    | [ IH: ∀ (A B C : ?Obj) f g h (t : ?F A),
        f ∘ g ≡ h →
        ?map B C f (?map A B g t) = ?map A C h t
      |- ?map _ _ _ (?map _ _ _ ?t) = ?map _ _ _ ?t
      ] => apply IH; auto_map_map_comp_arrow_eq Heq
    | |- fmap _ (fmap _ ?t) = fmap _ ?t =>
      apply map_map_comp; auto_map_map_comp_arrow_eq Heq
    | |- ?map _ _ _ (?map _ _ _ ?t) = ?map _ _ _ ?t =>
      apply map_map_comp; auto_map_map_comp_arrow_eq Heq
    | _ => idtac
    end
  end.

Create HintDb auto_bind_map_comp.
(*
Local Ltac auto_bind_map_comp_subst_eq Heq :=
  exact Heq || (apply Heq; fail) ||
  match goal with
  | |- subst_eq
         (subst_comp (liftS ?f) (subst_of_arr (liftA ?g)))
         (arrow_subst_comp (liftA ?g') (liftS ?f')) =>
    apply liftS_liftA_comp; auto_bind_map_comp_subst_eq Heq
  | _ => idtac
  end.

Ltac auto_bind_map_comp :=
  let Heq := fresh "Heq" in
  intro Heq;
  match goal with
  | |- ?bnd _ _ ?f (?map _ _ ?g ?t) = ?map _ _ ?g' (?bnd _ _ ?f' ?t) =>
    destruct t;
    simpl; try (autorewrite with auto_bind_map_comp; simpl);
    try (apply Heq; fail);
    try (solve_equal; try (apply Heq; fail);
    match goal with
    | [ IH: ∀ (A B B' C : ?Obj) f g g' f' (t : ?F A),
        subst_eq (subst_comp f (of_arrow g)) (arrow_subst_comp g' f') →
        ?bnd _ _ f (?map _ _ g t) = ?map _ _ g' (?bnd _ _ f' t)
      |- ?bnd _ _ _ (?map _ _ _ ?t) = ?map _ _ _ (?bnd _ _ _ ?t)
      ] => apply IH; auto_bind_map_comp_subst_eq Heq
    | |- bind _ (fmap _ ?t) = fmap _ (bind _ ?t) =>
      apply bind_map_comp; auto_bind_map_comp_subst_eq Heq
    | |- ?bind _ _ _ (?fmap _ _ _ ?t) = ?fmap _ _ _ (?bind _ _ _ ?t) =>
      apply bind_map_comp; auto_bind_map_comp_subst_eq Heq
    | _ => idtac
    end)
  end.
*)
Local Ltac auto_bind_pure_subst_eq Heq :=
  exact Heq ||
  match goal with
  | |- _ ↑ ≡ ı =>
    apply lift_id; auto_bind_pure_subst_eq Heq
  | _ => idtac
  end.

Local Ltac auto_bind_pure_loop Heq :=
  match goal with
  | [ IH: ∀ (A : ?Obj) f (t : ?F A),
      f ≡ ı → ?bnd A A f t = t
    |- context[ ?bnd _ _ _ ?t ]
    ] =>
      rewrite IH; [ auto_bind_pure_loop Heq | auto_bind_pure_subst_eq Heq ]
  | |- context[ bind _ ?t ] =>
      rewrite bind_pure;
      [ auto_bind_pure_loop Heq | auto_bind_pure_subst_eq Heq ]
  | _ => idtac
  end.

Ltac auto_bind_pure :=
  let Heq := fresh "Heq" in
  intro Heq;
  match goal with
  | |- ?bnd _ _ ?f ?t = ?t =>
    destruct t; term_simpl;
    try (apply Heq; fail);
    ((solve_equal;
      match goal with
      | [ IH: ∀ (A : ?Obj) f (t : ?F A),
          f ≡ ı → ?bnd A A f t = t
        |- ?bnd _ _ _ ?t = ?t
        ] => apply IH; auto_bind_pure_subst_eq Heq
      | |- bind _ ?t = ?t =>
        apply bind_pure; auto_bind_pure_subst_eq Heq
      | |- ?bind _ _ _ ?t = ?t =>
        apply bind_pure; auto_bind_pure_subst_eq Heq
      | _ => idtac
      end)
    || auto_bind_pure_loop Heq)
  end.

Create HintDb auto_bind_bind_comp.

Local Ltac auto_bind_bind_comp_subst_eq Heq :=
  exact Heq || (apply Heq; fail) ||
  match goal with
  | |- _ ↑ ∘ _ ↑ ≡ _ ↑ =>
    apply lift_comp; auto_bind_bind_comp_subst_eq Heq
  | _ => idtac
  end.

Ltac auto_bind_bind_comp :=
  let Heq := fresh "Heq" in
  intro Heq;
  match goal with
  | |- ?bnd _ _ ?f (?bnd _ _ ?g ?t) = ?bnd _ _ ?h ?t =>
    destruct t;
    term_simpl; try (autorewrite with auto_bind_bind_comp; simpl);
    try (apply Heq; fail);
    try (solve_equal; try (apply Heq; fail);
    match goal with
    | [ IH: ∀ (A B C : ?Obj) f g h (t : ?F A),
        f ∘ g ≡ h →
        ?bnd B C f (?bnd A B g t) = ?bnd A C h t
      |- ?bnd _ _ _ (?bnd _ _ _ ?t) = ?bnd _ _ _ ?t
      ] => apply IH; auto_bind_bind_comp_subst_eq Heq
    | |- bind _ (bind _ ?t) = bind _ ?t =>
      apply bind_bind_comp; auto_bind_bind_comp_subst_eq Heq
    | |- ?bind _ _ _ (?bind _ _ _ ?t) = ?bind _ _ _ ?t =>
      apply bind_bind_comp; auto_bind_bind_comp_subst_eq Heq
    | _ => idtac
    end)
  end.

(*
Ltac auto_ASLiftable :=
  unfold ASLiftable; intros; simpl;
  unfold bind, fmap; simpl; fold_fmap;
  rewrite fmap_liftA_shift_comm;
  apply f_equal;
  try match goal with
      | H: subst_eq ?f ?g |- _ => apply H
      end.
*)
*)
