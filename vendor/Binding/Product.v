Require Import Utf8.
Require Import Binding.Lib.

Record sprod (U₁ U₂ : Type) : Type :=
  { π₁ : U₁
  ; π₂ : U₂
  }.

Arguments π₁ {U₁ U₂}.
Arguments π₂ {U₁ U₂}.

Notation "U₁ × U₂" := (sprod U₁ U₂) (at level 40) : type_scope.
Notation "⟨ A , B ⟩" := {| π₁ := A ; π₂ := B |} : bind_scope.

Section Defs.
  Context {U₁ U₂ : Type} {Arr₁ : U₁ → U₁ → Type} {Arr₂ : U₂ → U₂ → Type}
          {EA₁ : EqIndCore Arr₁} {EA₂ : EqIndCore Arr₂} {EqA₁ : EqInd Arr₁} {EqA₂ : EqInd Arr₂}
          {AC₁ : ArrowCore Arr₁} {AC₂ : ArrowCore Arr₂} {AR₁ : Arrow Arr₁} {AR₂ : Arrow Arr₂}.

  Local Open Scope bind_scope.
  Import ArrowNotations.

  Record prod_arr {X Y : U₁ × U₂} : Type :=
    { arr₁ : Arr₁ (π₁ X) (π₁ Y);
      arr₂ : Arr₂ (π₂ X) (π₂ Y)
    }.
  Global Arguments prod_arr X Y : clear implicits.

  Notation " f × g " := {| arr₁ := f ; arr₂ := g |} (at level 40) : bind_scope.

  Global Instance EIC_prod : EqIndCore prod_arr :=
    λ A B f g, arr₁ f ≡ arr₁ g ∧ arr₂ f ≡ arr₂ g.

  Global Instance ArrowCore_vsig_arr : ArrowCore prod_arr :=
    {| arrow_id A := ı × ı;
       arrow_comp A B C f g := (arr₁ f ∘ arr₁ g) × (arr₂ f ∘ arr₂ g) |}.

  Global Instance Eq_prod : EqInd prod_arr.
  Proof.
    split; split; intros.
    - split; reflexivity.
    - split; symmetry; apply H.
    - split; etransitivity; now (apply H || apply H0).
  Qed.

  Global Instance Arrow_prod_arr : Arrow prod_arr.
  Proof.
    split; intros.
    - split; apply arrow_comp_id_l.
    - split; apply arrow_comp_id_r.
    - split; apply arrow_comp_assoc.
    - split; eapply arrow_comp_proper; now (apply H0 || apply H).
  Qed.

  Definition at₁ {A B : U₁} {C : U₂} (f : A [→] B) : ⟨A, C⟩ [→] ⟨B, C⟩ :=
    (f : π₁ ⟨A, C⟩ [→] π₁ ⟨B, C⟩) × ı.
  Definition at₂ {A : U₁} {B C : U₂} (f : B [→] C) : ⟨A, B⟩ [→] ⟨A, C⟩ :=
    ı × (f : π₂ ⟨A, B⟩ [→] π₂ ⟨A, C⟩).

  Section ALift.
    Context (F₁ : U₁ → U₁) (F₂ : U₂ → U₂) {ALC₁ : LiftableCore Arr₁ F₁}
            {ALC₂ : LiftableCore Arr₂ F₂} {AL₁ : Liftable Arr₁ F₁} {AL₂ : Liftable Arr₂ F₂}.

    Definition on₁ (X : U₁ × U₂) := ⟨ F₁ (π₁ X), π₂ X ⟩.
    Definition on₂ (X : U₁ × U₂) := ⟨ π₁ X, F₂ (π₂ X) ⟩.

    Global Instance ALC_prod_left : LiftableCore prod_arr on₁ :=
      { lift A B f := (arr₁ f) ↑ × (arr₂ f : π₂ (on₁ A) [→] π₂ (on₁ B))}.

    Global Instance AL_prod_left : Liftable prod_arr on₁.
    Proof.
      split; intros.
      - split; simpl; [apply lift_id |]; apply EQ.
      - split; simpl; [apply lift_comp |]; apply EQ.
      - split; simpl; [apply lift_proper |]; apply H.
    Qed.

    Global Instance ALC_prod_right : LiftableCore prod_arr on₂ :=
      { lift A B f := (arr₁ f : π₁ (on₂ A) [→] π₁ (on₂ B)) × (arr₂ f) ↑}.

    Global Instance AL_prod_right : Liftable prod_arr on₂.
    Proof.
      split; intros.
      - split; simpl; [| apply lift_id]; apply EQ.
      - split; simpl; [| apply lift_comp]; apply EQ.
      - split; simpl; [| apply lift_proper]; apply H.
    Qed.

  End ALift.

  Section Shift.
    Context (Inc₁ : U₁ → U₁) (Inc₂ : U₂ → U₂)
            {SC₁ : ShiftableCore Arr₁ Inc₁} {SC₂ : ShiftableCore Arr₂ Inc₂}.

    Global Instance SC_prod_left : ShiftableCore prod_arr (on₁ Inc₁) :=
      { mk_shift := λ A, mk_shift × ı }.

    Global Instance SC_prod_right : ShiftableCore prod_arr (on₂ Inc₂) :=
      { mk_shift := λ A, ı × mk_shift }.

  End Shift.

  Section LiftA_Shift.
    Context (F₁ : U₁ → U₁) (F₂ : U₂ → U₂)
            {ALC₁ : LiftableCore Arr₁ F₁} {ALC₂ : LiftableCore Arr₂ F₂}
            {AL₁ : Liftable Arr₁ F₁} {AL₂ : Liftable Arr₂ F₂}
            {SC₁ : ShiftableCore Arr₁ F₁} {SC₂ : ShiftableCore Arr₂ F₂}
            {LAS₁ : LiftAShift Arr₁ F₁} {LAS₂ : LiftAShift Arr₂ F₂}.

    Global Instance LiftAShift_prod_left : LiftAShift prod_arr (on₁ F₁).
    Proof.
      intros A B f; split; simpl.
      - apply LAS₁.
      - etransitivity; [ apply arrow_comp_id_r | ].
        symmetry; apply arrow_comp_id_l.
    Qed.


    Global Instance LiftAShift_prod_right : LiftAShift prod_arr (on₂ F₂).
    Proof.
      intros A B f; split; simpl.
      - etransitivity; [ apply arrow_comp_id_r | ].
        symmetry; apply arrow_comp_id_l.
      - apply LAS₂.
    Qed.
  End LiftA_Shift.

End Defs.

Notation " f × g " := {| arr₁ := f ; arr₂ := g |} (at level 40) : bind_scope.
