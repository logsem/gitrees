Require Import Utf8.
Require Import Binding.Core.
Require Import Binding.Properties.

Create HintDb term_simpl.
Create HintDb term_simpl_raw.

Ltac fold_fmap_goal :=
  repeat match goal with
  | |- context[ ?map ?A ?B ?f ?t ] =>
    match map with
    | @fmap ?Obj ?Arr ?F ?m => fail 1
    | _ =>
      match type of map with
      | ∀ A B : ?Obj, ?Arr A B → ?F A → ?F B =>
          change (map A B f t) with (fmap f t) ||
          change (map A B f t) with (fmap (Obj := Obj) (F := F) f t)
      | FunctorCore _ =>
          change (map A B f t) with (fmap (FunctorCore := map) f t)
      end
    end
  end.

Ltac fold_fmap_in H :=
  repeat match type of H with
  | context[ ?map ?A ?B ?f ?t ] =>
    match map with
    | @fmap ?Obj ?Arr ?F ?m => fail 1
    | _ =>
      match type of map with
      | ∀ A B : ?Obj, ?Arr A B → ?F A → ?F B =>
          change (map A B f t) with (fmap f t) in H ||
          change (map A B f t) with (fmap (Obj := Obj) (F := F) f t) in H
      | FunctorCore _ =>
          change (map A B f t) with (fmap (FunctorCore := map) f t) in H
      end
    end
  end.

Tactic Notation "fold_fmap" := fold_fmap_goal.
Tactic Notation "fold_fmap" "in" hyp(H) := fold_fmap_in H.

Ltac fold_bind_goal :=
  repeat match goal with
  | |- context[ ?bnd ?A ?B ?f ?t ] =>
    match bnd with
    | @bind ?Obj ?Sub ?F ?b => fail 1
    | _ =>
      match type of bnd with
      | ∀ A B : ?Obj, _ → ?F A → ?F B =>
          change (bnd A B f t) with (bind f t) ||
          change (bnd A B f t) with (bind (Obj := Obj) (F := F) f t)
      | BindCore _ =>
          change (bnd A B f t) with (bind (BindCore := bnd) f t)
      end
    end
  end.

Ltac fold_bind_in H :=
  repeat match type of H with
  | context[ ?bnd ?A ?B ?f ?t ] =>
    match bnd with
    | @bind ?Obj ?Sub ?F ?b => fail 1
    | _ =>
      match type of bnd with
      | ∀ A B : ?Obj, _ → ?F A → ?F B =>
          change (bnd A B f t) with (bind f t) in H ||
          change (bnd A B f t) with (bind (Obj := Obj) (F := F) f t) in H
      | BindCore _ =>
          change (bnd A B f t) with (bind (BindCore := bnd) f t) in H
      end
    end
  end.

Tactic Notation "fold_bind" := fold_bind_goal.
Tactic Notation "fold_bind" "in" hyp(H) := fold_bind_in H.

Ltac fold_fmap_and_bind_goal :=
  repeat match goal with
  | |- context[ ?ff ?A ?B ?f ?t ] =>
    match ff with
    | @fmap ?Obj ?Arr ?F ?m => fail 1
    | @bind ?Obj ?Sub ?F ?m => fail 1
    | _ =>
      match type of ff with
      | ∀ A B : ?Obj, _ → ?F A → ?F B =>
          change (ff A B f t) with (fmap f t) ||
          change (ff A B f t) with (fmap (Obj := Obj) (F := F) f t) ||
          change (ff A B f t) with (bind f t) ||
          change (ff A B f t) with (bind (Obj := Obj) (F := F) f t)
      | FunctorCore _ =>
          change (ff A B f t) with (fmap (FunctorCore := ff) f t)
      | BindCore _ =>
          change (ff A B f t) with (bind (BindCore := ff) f t)
      end
    end
  end.

Ltac fold_fmap_and_bind_in H :=
  repeat match type of H with
  | context[ ?ff ?A ?B ?f ?t ] =>
    match ff with
    | @fmap ?Obj ?Arr ?F ?m => fail 1
    | @bind ?Obj ?Sub ?F ?m => fail 1
    | _ =>
      match type of ff with
      | ∀ A B : ?Obj, _ → ?F A → ?F B =>
          change (ff A B f t) with (fmap f t) in H ||
          change (ff A B f t) with (fmap (Obj := Obj) (F := F) f t) in H ||
          change (ff A B f t) with (bind f t) in H ||
          change (ff A B f t) with (bind (Obj := Obj) (F := F) f t) in H
      | FunctorCore _ =>
          change (ff A B f t) with (fmap (FunctorCore := ff) f t) in H
      | BindCore _ =>
          change (ff A B f t) with (bind (BindCore := ff) f t) in H
      end
    end
  end.

Tactic Notation "fold_fmap_and_bind" := fold_fmap_and_bind_goal.
Tactic Notation "fold_fmap_and_bind" "in" hyp(H) := fold_fmap_and_bind_in H.

Ltac fold_shift_goal :=
  repeat match goal with
  | |- context[ @fmap ?Obj ?Arr ?G ?MF ?A _
         (@mk_shift ?Obj _ ?Inc ?Sh ?A)
         ?t
       ] =>
    change (@fmap Obj Arr G MF A _ (@mk_shift Obj _ Inc Sh A) t)
    with (@shift Obj Arr G MF Inc Sh A t)
  end.

Ltac fold_shift_in H :=
  repeat match type of H with
  | context[ @fmap ?Obj ?Arr ?G ?MF ?A _
      (@mk_shift ?Obj _ ?Inc ?Sh ?A)
      ?t
    ] =>
    change (@fmap Obj Arr G MF A _ (@mk_shift Obj _ Inc Sh A) t)
    with (@shift Obj Arr G MF Inc Sh A t) in H
  end.

Tactic Notation "fold_shift" := fold_shift_goal.
Tactic Notation "fold_shift" "in" hyp(H) := fold_shift_in H.

Ltac fold_subst_goal :=
  repeat match goal with
  | |- context[ @bind ?Obj ?Sub ?G ?BF _ ?A
         (@mk_subst ?Obj _ ?F ?Inc ?Sb ?A ?v)
         ?t
       ] =>
    change (@bind Obj Sub G BF _ A (@mk_subst Obj _ F Inc Sb A v) t)
    with (@subst Obj Sub G BF F Inc Sb A t v)
  end.

Ltac fold_subst_in H :=
  repeat match type of H with
  | context[ @bind ?Obj ?Sub ?G ?BF _ ?A
      (@mk_subst ?Obj _ ?F ?Inc ?Sb ?A ?v)
      ?t
    ] =>
    change (@bind Obj Sub G BF _ A (@mk_subst Obj _ F Inc Sb A v) t)
    with (@subst Obj Sub G BF F Inc Sb A t v) in H
  end.

Tactic Notation "fold_subst" := fold_subst_goal.
Tactic Notation "fold_subst" "in" hyp(H) := fold_subst_in H.

Ltac term_simpl_goal :=
  repeat (
    unfold subst, shift, bind, fmap; simpl;
    repeat (autorewrite with term_simpl_raw; simpl);
    fold_fmap_and_bind; fold_shift; fold_subst;
    repeat match goal with
    | |- context[ fmap ?f (subst ?t ?v) ] => rewrite (fmap_subst f t v)
    | |- context[ fmap (lift (G:=?Inc) ?f) (shift (Inc:=?Inc) ?t) ] =>
      rewrite (fmap_liftA_shift_comm f t)
    | |- context[ bind ?f (subst ?t ?v) ] => rewrite (bind_subst f t v)
    | |- context[ bind (lift (G:=?Inc) ?f) (shift (Inc:=?Inc) ?t) ] =>
      rewrite (bind_liftS_shift_comm f t)
    | |- context[ subst (Inc:=?Inc) (shift (Inc:=?Inc) ?t) ?v ] =>
      rewrite (subst_shift_id t v)
    end;
    try autorewrite with term_simpl
  ).

Ltac term_simpl_in H :=
  repeat (
    unfold subst, shift, bind, fmap in H; simpl in H;
    repeat (autorewrite with term_simpl_raw in H; simpl in H);
    fold_fmap_and_bind in H; fold_shift in H; fold_subst in H;
    repeat match type of H with
    | context[ fmap ?f (subst ?t ?v) ] => rewrite (fmap_subst f t v) in H
    | context[ fmap (lift (G:=?Inc) ?f) (shift (Inc:=?Inc) ?t) ] =>
      rewrite (fmap_liftA_shift_comm f t) in H
    | context[ bind ?f (subst ?t ?v) ] => rewrite (bind_subst f t v) in H
    | context[ bind (lift (G:=?Inc) ?f) (shift (Inc:=?Inc) ?t) ] =>
      rewrite (bind_liftS_shift_comm f t) in H
    | context[ subst (Inc:=?Inc) (shift (Inc:=?Inc) ?t) ?v ] =>
      rewrite (subst_shift_id t v) in H
    end;
    try autorewrite with term_simpl in H
  ).

Tactic Notation "term_simpl" := term_simpl_goal.
Tactic Notation "term_simpl" "in" hyp(H) := term_simpl_in H.
