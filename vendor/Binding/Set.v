Require Import Utf8.
Require Import Binding.Core.
Require Import Binding.Inc.
Require Import Binding.Properties.
Require Import Morphisms.

Class SetPureCore (F : Set → Type) : Type :=
  set_pure : ∀ A : Set, A → F A.

Arguments set_pure {F _ A}.

Record Arr (A B : Set) : Type :=
  { apply_arr : A → B
  }.
Notation " A '[→]' B " := (Arr A B) (at level 100, no associativity) : type_scope.

Arguments apply_arr {A B}.
Coercion apply_arr : Arr >-> Funclass.

Record Sub {F : Set → Type} {FP : SetPureCore F} (A B : Set) : Type :=
  { apply_sub : A → F B
  }.
Notation " A '[⇒]' B " := (Sub A B) (at level 100, no associativity) : type_scope.

Arguments apply_sub {F FP A B}.
Coercion apply_sub : Sub >-> Funclass.

Global Instance ArrEqC : EqIndCore Arr :=
  λ A B f g, ∀ x, f x = g x.

Global Instance ArrEq : EqInd Arr.
Proof.
  split; intros; split; intros; congruence.
Qed.

Global Instance SubEqC {F} {FP : SetPureCore F} : EqIndCore Sub :=
  λ A B f g, ∀ x, f x = g x.

Global Instance SubEq {F} {FP : SetPureCore F} : EqInd Sub.
Proof.
  split; split; intros; congruence.
Qed.

Global Instance ArrowCore_Set : ArrowCore Arr :=
  { arrow_id   := λ _,         {| apply_arr := λ x, x       |}
  ; arrow_comp := λ _ _ _ f g, {| apply_arr := λ x, f (g x) |}
  }.

Class SetPure (F : Set → Type) {FP : SetPureCore F}
    {MapF : FunctorCore F}
    {BndF : BindCore F} : Prop :=
  { fmap_set_pure : ∀ (A B : Set) (f : Arr A B) (x : A),
      fmap f (set_pure x) = set_pure (f x)
  ; bind_set_pure : ∀ (A B : Set) (f : Sub A B) (x : A),
      bind f (set_pure x) = f x
  }.

Section SetInstances.
  Context {F : Set → Type} {FP : SetPureCore F}.
  Context {MapF : FunctorCore (Arr := Arr) F}.
  Context {BndF : BindCore (Sub := Sub) F}.
  Context {SPF : SetPure F}.

  Global Instance Arrow_Set : Arrow Arr.
  Proof.
    split; [unfold equal, ArrEqC; simpl; congruence .. |].
    intros A B C f₁ f₂ EQf g₁ g₂ EQg x; simpl; congruence.
  Qed.

  Global Instance SubstArrCore_Set : ArrowCore Sub :=
    { arrow_id A := {| apply_sub := set_pure |};
      arrow_comp A B C f g := {| apply_sub := λ x, bind f (g x) |} }.

  Global Instance SubstCore_Set : SubstCore Arr Sub :=
    λ A B f, {| apply_sub := λ x, set_pure (f x) |}.

  Definition incFun (A B : Set) (f : Arr A B) : inc A → inc B := inc_map f.

  Global Instance IncMap : FunctorCore inc := incFun.
  Global Instance IncFun : Functor inc.
  Proof.
    split; intros.
    - destruct t as [| x]; unfold fmap; simpl; f_equal; apply EQ.
    - destruct t as [| x]; unfold fmap; simpl; f_equal; apply EQ.
  Qed.

  Context {MF : Functor F} {BF : Bind F}.
  Context {BMPF : BindMapPure F} {BMCF : BindMapComm F}.

  Global Instance SubArrow_Set : Arrow Sub.
  Proof.
    split; simpl; intros.
    - intros x; simpl; apply bind_pure; reflexivity.
    - intros x; simpl; apply bind_set_pure.
    - intros x; simpl; symmetry; apply bind_bind_comp; reflexivity.
    - intros ρ₁ ρ₂ EQρ σ₁ σ₂ EQσ x; simpl; rewrite EQσ; clear EQσ.
      etransitivity; [| apply bind_pure; reflexivity].
      symmetry; apply bind_bind_comp.
      intros y; rewrite EQρ; apply bind_pure; reflexivity.
  Qed.

  Global Instance Subst_Set : Subst Arr Sub.
  Proof.
    split; intros.
    - reflexivity.
    - intros x; simpl; symmetry; apply bind_set_pure.
    - intros f g EQ x; simpl; congruence.
  Qed.

  Global Instance ALiftableCore_inc : LiftableCore Arr inc :=
    { lift A B f := {| apply_arr := fmap f |} }.

  Global Instance ALiftable_inc : Liftable Arr inc.
  Proof.
    split; intros.
    - intros x; simpl; apply map_id, EQ.
    - intros x; simpl; apply map_map_comp, EQ.
    - intros f₁ f₂ EQf x; simpl; now rewrite EQf.
  Qed.

  Global Instance ShiftableCore_inc : ShiftableCore Arr inc :=
    λ A, {| apply_arr := VS |}.

  Global Instance LiftAShift_inc : LiftAShift Arr inc.
  Proof.
    unfold LiftAShift; reflexivity.
  Qed.

  Global Instance SLiftableCore_inc : LiftableCore Sub inc :=
    { lift A B f :=
        {| apply_sub := λ x,
                        match x with
                        | VZ   => set_pure VZ
                        | VS y => shift (f y)
                        end
        |}
    }.

  Global Instance LiftSShift_inc : LiftSShift Arr Sub inc.
  Proof.
    intros A B f x; simpl.
    rewrite bind_set_pure; simpl.
    unfold shift; simpl; rewrite map_to_bind; reflexivity.
  Qed.

  Global Instance SLiftable_inc : Liftable Sub inc.
  Proof.
    split; intros.
    - intros [| x]; simpl; [reflexivity | unfold shift; simpl].
      rewrite EQ; apply fmap_set_pure.
    - intros [| x]; simpl; [now apply bind_set_pure |].
      rewrite bind_liftS_shift_comm, <- EQ; reflexivity.
    - intros f₁ f₂ EQf [| x]; simpl; [reflexivity | now rewrite EQf].
  Qed.

  Global Instance ASLiftInj_inc : ASLiftInj Arr Sub inc.
  Proof.
    intros A B f g EQ [| x]; simpl; [reflexivity |].
    rewrite <- EQ; simpl; symmetry; apply fmap_set_pure.
  Qed.

  Global Instance ASLiftComm_inc : ASLiftComm Arr Sub inc.
  Proof.
    intros A B₁ B₂ C f₁ f₂ g₁ g₂ EQ [| x]; simpl.
    - rewrite !bind_set_pure; simpl; reflexivity.
    - rewrite bind_set_pure; simpl.
      unfold shift; erewrite <- map_to_bind, map_map_comp by apply liftA_mk_shift_comm.
      rewrite <- map_map_comp'; f_equal.
      specialize (EQ x); simpl in EQ.
      now rewrite bind_set_pure, <- map_to_bind in EQ.
  Qed.

  Global Instance SubstitutableCore_inc : SubstitutableCore Sub F inc :=
    λ A v,
    {| apply_sub := λ x,
                    match x with
                    | VZ => v
                    | VS y => set_pure y
                    end
    |}.

  Global Instance SubstShift_inc : SubstShift Arr Sub F inc.
  Proof.
    intros A v x; simpl.
    rewrite bind_set_pure; reflexivity.
  Qed.

  Global Instance SubstFMap_inc : SubstFMap Arr Sub F inc.
  Proof.
    intros A B f v [ | x ]; simpl.
    - rewrite bind_set_pure; simpl; rewrite <- map_to_bind; reflexivity.
    - rewrite !bind_set_pure; reflexivity.
  Qed.

  Global Instance SubstBind_inc : SubstBind Sub F inc.
  Proof.
    intros A B f v [| x]; simpl.
    - rewrite bind_set_pure; reflexivity.
    - rewrite bind_set_pure; symmetry; apply subst_shift_id.
  Qed.

End SetInstances.

Arguments set_pure {F _ A} /.
