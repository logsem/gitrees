Require Import Utf8.
Require Import Binding.Core.
Require Import Binding.Inc.
Require Import Binding.Properties.
Require Import Morphisms.

Record Ctx {V : Type} :=
  {dom : Set;
   arr :> dom -> V
  }.
Arguments Ctx V : clear implicits.

Definition mtC {V : Type} : Ctx V :=
  {| dom := Empty_set;
     arr x := match x with end
  |}.

Definition extC {V : Type} (v : V) (Γ : Ctx V) : Ctx V :=
  {| dom := inc (dom Γ);
     arr x := match x with
              | VZ => v
              | VS x => Γ x
              end
  |}.

Notation "'ε'" := mtC.
Notation "Γ ▹ v" := (extC v Γ) (at level 40, left associativity).

Class IntPureCore {V : Type} (F : V → Ctx V → Type) : Type :=
  int_pure : ∀ (Γ : Ctx V) v (x : dom Γ) (EQ : Γ x = v) , F v Γ.

Arguments int_pure {V F _ Γ}.

Record Arr {V : Type} {Γ Δ : Ctx V} : Type :=
  { apply_arr : dom Γ → dom Δ;
    arr_hom   : ∀ x : dom Γ, Δ (apply_arr x) = Γ x
  }.
Arguments Arr {V} Γ Δ.
Notation " A '[→]' B " := (Arr A B) (at level 100, no associativity) : type_scope.
Coercion apply_arr : Arr >-> Funclass.

Record Sub {V} {F : V → Ctx V → Type} {FP : IntPureCore F} (Γ Δ : Ctx V) : Type :=
  { apply_sub : ∀ v (x : dom Γ) (EQ : Γ x = v), F v Δ
  }.
Notation " A '[⇒]' B " := (Sub A B) (at level 100, no associativity) : type_scope.

Arguments apply_sub {V F FP Γ Δ}.
Coercion apply_sub : Sub >-> Funclass.

Global Instance ArrEqC {V} : EqIndCore (Arr (V := V)) :=
  λ A B f g, ∀ x, f x = g x.

Global Instance ArrEq {V} : EqInd (Arr (V := V)).
Proof.
  split; intros; split; intros; congruence.
Qed.

Global Instance SubEqC {V F} {FP : IntPureCore (V := V) F} : EqIndCore Sub :=
  λ A B f g, ∀ v x EQ, f v x EQ = g v x EQ.

Global Instance SubEq {V F} {FP : IntPureCore (V := V) F} : EqInd Sub.
Proof.
  split; split; intros; congruence.
Qed.

Global Program Instance ArrowCore_Set {V} : ArrowCore (Arr (V := V)) :=
  { arrow_id   := λ _,         {| apply_arr := λ x, x       |}
  ; arrow_comp := λ _ _ _ f g, {| apply_arr := λ x, f (g x) |}
  }.
Next Obligation.
  etransitivity; apply arr_hom.
Defined.

Class IntPure {V} (F : V → Ctx V → Type) {FP : IntPureCore (V := V) F}
    {MapF : ∀ v, FunctorCore (F v)}
    {BndF : ∀ v, BindCore (Sub := Sub) (F v)} : Prop :=
  { fmap_int_pure : ∀ (Γ Δ : Ctx V) (f : Arr Γ Δ) v (x : dom Γ) (EQ : Γ x = v),
        fmap f (int_pure v x EQ) = int_pure v (f x) (eq_trans (arr_hom f x) EQ)
  ; bind_set_pure : ∀ (Γ Δ : Ctx V) (f : Sub Γ Δ) v (x : dom Γ) (EQ : Γ x = v),
      bind f (int_pure (IntPureCore := FP) v x EQ) = f v x EQ
  }.

Section IntInstances.
  Context {V} {F : V → Ctx V → Type} {FP : IntPureCore F}.
  Context {MapF : ∀ v, FunctorCore (Arr := Arr) (F v)}.
  Context {BndF : ∀ v, BindCore (Sub := Sub) (F v)}.
  Context {SPF : IntPure F}.

  Global Instance Arrow_Int : Arrow (Arr (V := V)).
  Proof.
    split; [unfold equal, ArrEqC; simpl; congruence .. |].
    intros A B C f₁ f₂ EQf g₁ g₂ EQg x; simpl; congruence.
  Qed.

  Global Instance SubstArrCore_Set : ArrowCore (Sub (V := V)) :=
    { arrow_id A := {| apply_sub := int_pure |};
      arrow_comp A B C f g := {| apply_sub := λ v x EQ, bind f (g v x EQ) |} }.

  Global Instance SubstCore_Set : SubstCore Arr Sub :=
    λ Γ Δ f, {| apply_sub := λ v x EQ, int_pure v (f x) (eq_trans (arr_hom f x) EQ) |}.

  Program Definition extFun v (Γ Δ : Ctx V) (f : Arr Γ Δ) : Arr (Γ ▹ v) (Δ ▹ v) :=
    {| apply_arr := inc_map f |}.
  Next Obligation.
    destruct x as [| x]; simpl; [reflexivity | apply arr_hom].
  Defined.

  Context {MF : ∀ v, Functor (F v)} {BF : ∀ v, Bind (F v)}.
  Context {BMPF : ∀ v, BindMapPure (F v)} {BMCF : ∀ v, BindMapComm (F v)}.

  Global Instance SubArrow_Set : Arrow Sub.
  Proof.
    split; simpl; intros.
    - intros v x EQ; simpl; apply bind_pure; reflexivity.
    - intros v x EQ; simpl; apply bind_set_pure.
    - intros v x EQ; simpl; symmetry; apply bind_bind_comp; reflexivity.
    - intros ρ₁ ρ₂ EQρ σ₁ σ₂ EQσ v x EQ; simpl; rewrite EQσ; clear EQσ.
      etransitivity; [| apply bind_pure; reflexivity].
      symmetry; apply bind_bind_comp.
      intros u y EQ'; rewrite EQρ; apply bind_pure; reflexivity.
  Qed.

  Global Instance Subst_Set : Subst Arr Sub.
  Proof.
    split; intros.
    - intros v x []; simpl; reflexivity.
    - intros v x []; simpl; symmetry; unfold ArrowCore_Set_obligation_2.
      generalize (g x) as y, (arr_hom g x).
      intros y []; simpl; apply bind_set_pure.
    - intros f g EQ v x EQ'; simpl.
      rewrite <- !fmap_int_pure, EQ; reflexivity.
  Qed.

  Global Instance ALiftableCore_ext {v : V} : LiftableCore Arr (extC v) :=
    { lift := extFun v }.

  Global Instance ALiftable_ext {v : V} : Liftable Arr (extC v).
  Proof.
    split; intros.
    - intros [| x]; simpl; [reflexivity | f_equal; apply EQ].
    - intros [| x]; simpl; [reflexivity | f_equal; apply EQ].
    - intros f₁ f₂ EQf [| x]; simpl; [reflexivity | f_equal; apply EQf].
  Qed.

  Global Program Instance ShiftableCore_ext {v : V} : ShiftableCore Arr (extC v) :=
    λ A, {| apply_arr := VS : dom A → dom (A ▹ v) |}.

  Global Instance LiftAShift_ext {v : V} : LiftAShift Arr (extC v).
  Proof.
    unfold LiftAShift; intros Γ Δ f x; reflexivity.
  Qed.

  Global Instance SLiftableCore_ext {v : V} : LiftableCore Sub (extC v) :=
    { lift Γ Δ ρ :=
        {| apply_sub := λ u (x : dom (Γ ▹ v)),
                        match x with
                        | VZ   => λ EQ, int_pure u (VZ : dom (Δ ▹ v)) EQ
                        | VS y => λ EQ, shift (ρ u y EQ)
                        end
        |}
    }.

  Global Instance LiftSShift_ext {v : V} : LiftSShift Arr Sub (extC v).
  Proof.
    intros A B f u x []; simpl.
    rewrite bind_set_pure.
    apply map_to_bind.
  Qed.

  Global Instance SLiftable_ext {v : V} : Liftable Sub (extC v).
  Proof.
    split; intros.
    - intros u [| x] []; simpl; [reflexivity | unfold shift; simpl].
      rewrite EQ; simpl.
      rewrite fmap_int_pure; simpl; reflexivity.
    - intros u [| x] []; simpl; [now apply bind_set_pure |].
      rewrite bind_liftS_shift_comm, <- EQ; reflexivity.
    - intros f₁ f₂ EQf u [| x] []; simpl; [reflexivity | now rewrite EQf].
  Qed.

  Global Instance ASLiftInj_ext {v : V} : ASLiftInj Arr Sub (extC v).
  Proof.
    intros A B f g EQ u [| x] []; simpl; [reflexivity |].
    rewrite <- EQ; simpl; symmetry.
    generalize (f x) as y, (arr_hom f x); intros y []; simpl.
    unfold shift; rewrite fmap_int_pure; reflexivity.
  Qed.

  Global Instance ASLiftComm_ext {v : V} : ASLiftComm Arr Sub (extC v).
  Proof.
    intros A B₁ B₂ C f₁ f₂ g₁ g₂ EQ u [| x] []; simpl.
    - etransitivity; [apply bind_set_pure |].
      rewrite bind_set_pure; reflexivity.
    - unfold shift; erewrite <- map_to_bind, map_map_comp by apply liftA_mk_shift_comm.
      rewrite <- map_map_comp'; specialize (EQ _ x eq_refl); simpl in EQ; rewrite <- map_to_bind in EQ.
      rewrite <- EQ; clear EQ.
      generalize (f₂ x) as y, (arr_hom f₂ x); intros y []; simpl.
      rewrite !bind_set_pure; reflexivity.
  Qed.

  Global Instance SubstitutableCore_ext {v : V} : SubstitutableCore Sub (F v) (extC v) :=
    λ A u,
    {| apply_sub := λ w (x : dom (A ▹ v)),
                    match x with
                    | VZ => λ EQ, match EQ with eq_refl => u end
                    | VS y => int_pure w y
                    end
    |}.

  Global Instance SubstShift_ext {v : V} : SubstShift Arr Sub (F v) (extC v).
  Proof.
    intros A u w x []; simpl.
    apply bind_set_pure.
  Qed.

  Global Instance SubstFMap_ext {v : V} : SubstFMap Arr Sub (F v) (extC v).
  Proof.
    intros A B f u w [ | x ] []; simpl.
    - rewrite <- map_to_bind, bind_set_pure; simpl; reflexivity.
    - rewrite !bind_set_pure; simpl; reflexivity.
  Qed.

  Global Instance SubstBind_ext {v : V} : SubstBind Sub (F v) (extC v).
  Proof.
    intros A B f u w [| x] []; simpl.
    - rewrite bind_set_pure; reflexivity.
    - rewrite bind_set_pure; symmetry; apply subst_shift_id.
  Qed.

End IntInstances.

Arguments int_pure {V F _ Γ v} /.
