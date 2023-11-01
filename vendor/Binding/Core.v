Require Import Utf8.
Require Import RelationClasses Morphisms.
Require Vector.

Declare Scope bind_scope.
Delimit Scope bind_scope with bind.
Local Open Scope bind_scope.

Section EqualityIndexedTypes.
  Context {Obj : Type}.

  Class EqIndCore (T : Obj → Obj → Type) :=
    equal A B : T A B → T A B → Prop.

  Class EqInd (T : Obj → Obj → Type) {EIC : EqIndCore T} :=
    { eq_equiv A B :> Equivalence (equal A B) }.

End EqualityIndexedTypes.

Notation " f ≡ g " := (equal _ _ f%bind g%bind) (at level 70, no associativity) : bind_scope.

(** * Arrows and maps *)
Section Arrows.
  Context {Obj : Type}.

  (** ** Arrows *)
  Class ArrowCore (Arr : Obj → Obj → Type) : Type :=
    { arrow_id A : Arr A A;
      arrow_comp {A B C} : Arr B C → Arr A B → Arr A C
    }.

  Definition arrow {Arr} {ArrEq : EqIndCore Arr} {AC : ArrowCore Arr} := Arr.

  Notation " 'ı' " := (arrow_id _) : bind_scope.
  Notation " f ∘ g " := (arrow_comp f%bind g%bind) (at level 40, left associativity) : bind_scope.

  Class Arrow (Arr : Obj → Obj → Type) {ArrEq : EqIndCore Arr} {AC : ArrowCore Arr} : Prop :=
    { arrow_comp_id_l {A B} (f : Arr A B) : ı ∘ f ≡ f;
      arrow_comp_id_r {A B} (f : Arr A B) : f ∘ ı ≡ f;
      arrow_comp_assoc {A B C D} (f : Arr C D) (g : Arr B C) (h : Arr A B) :
        f ∘ g ∘ h ≡ f ∘ (g ∘ h);
      arrow_comp_proper
        A B C :> Proper (equal B C ==> equal A B ==> equal A C) arrow_comp}.

  Context {Arr : Obj → Obj → Type} {ArrEq : EqIndCore Arr} {AC : ArrowCore Arr}.

  (** ** Maps *)

  Class FunctorCore (F : Obj → Type) :=
    fmap : ∀ {A B}, (Arr A B) → F A → F B.

  (*Definition fmap {F : Obj → Type}
             {FunCore : FunctorCore F} {A B : Obj}
             (f : Arr A B) : F A → F B := fmap_core _ _ f.*)

  Class Functor (F : Obj → Type) {FunCore : FunctorCore F} : Prop :=
    { map_id {A} (f : Arr A A) (t : F A) (EQ : f ≡ ı) :
        fmap f t = t;
      map_map_comp {A B C} (f : Arr B C) (g : Arr A B) h (t : F A)
                   (EQ : f ∘ g ≡ h) :
        fmap f (fmap g t) = fmap h t}.

End Arrows.

(* Repeat notations due to section locality nonsense *)
Module ArrowNotations.
  Notation " A '[→]' B " := (arrow A B) (at level 100, no associativity) : type_scope.
End ArrowNotations.
  
Notation " 'ı' " := (arrow_id _) : bind_scope.
Notation " f ∘ g " := (arrow_comp f%bind g%bind) (at level 40, left associativity) : bind_scope.

(** * Substitutions and binds *)
Section Substitutions.
  Context {Obj : Type}.

  (** ** Substitutions *)
  Class SubstCore (Arr : Obj → Obj → Type) (Sub : Obj → Obj → Type) : Type :=
    subst_of_arr : ∀ {A B}, Arr A B → Sub A B.

  Definition sub {Arr Sub} {ASC : SubstCore Arr Sub} := Sub.
  Definition subarr {Arr Sub} {ASC : SubstCore Arr Sub} := Arr.

  (*Notation " 'η' " := (subst_pure _) : bind_scope.
  Notation " σ • ρ " := (subst_comp σ%bind ρ%bind) (at level 40, left associativity) : bind_scope.*)
  Notation " f '̂' " := (subst_of_arr f%bind) (at level 30) : bind_scope.

  Class Subst
        (Arr : Obj → Obj → Type) {ArrEq : EqIndCore Arr} {AC : ArrowCore Arr}
        (Sub : Obj → Obj → Type) {SubEq : EqIndCore Sub} {SC : ArrowCore Sub}
        {ASC : SubstCore Arr Sub}  : Prop :=
    { arrow_subst_id {A} : ı ̂ ≡ (ı : Sub A A);
      arrow_subst_comp {A B C} (f : Arr B C) (g : Arr A B) :
        (f ∘ g)̂ ≡ f ̂ ∘ g ̂;
      arrow_subst_proper A B :> Proper (equal A B ==> equal A B) subst_of_arr}.

    (** ** Binding *)

    Context {Arr : Obj → Obj → Type} {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}.
    Context {Sub : Obj → Obj → Type} {EqSub : EqIndCore Sub} {SC : ArrowCore Sub}.
    Context {ASC : SubstCore Arr Sub}.

    Class BindCore (F : Obj → Type) :=
      bind : ∀ {A B}, (Sub A B) → F A → F B.

    (*Definition bind {F : Obj → Type}
               {BindF : BindCore F} {A B : Obj}
               (f : Sub A B) : F A → F B := bind_core _ _ f.*)

    Class BindMapPure (F : Obj → Type) {MapF : FunctorCore F} {BindF : BindCore F} : Prop :=
      { bind_map {A B} (f : Arr A B) g t
                 (EQ : f ̂ ≡ g) :
          fmap f t = bind g t
      }.

    Class BindMapComm (F : Obj → Type) {MapF : FunctorCore F} {BindF : BindCore F} : Prop :=
      { bind_map_comm {A B₁ B₂ C} (f₁ : Arr B₁ C) (f₂ : Arr A B₂) (g₁ : Sub A B₁) g₂ t
                 (EQ : g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁) :
          bind g₂ (fmap f₂ t) = fmap f₁ (bind g₁ t)
      }.

    Class Bind (F : Obj → Type) {BindF : BindCore F} : Prop :=
      { bind_pure {A} (f : Sub A A) (t : F A) (EQ : f ≡ ı) :
          bind f t = t;
        bind_bind_comp {A B C} (f : Sub B C) (g : Sub A B) h (t : F A)
                       (EQ : f ∘ g ≡ h) :
          bind f (bind g t) = bind h t
      }.

End Substitutions.

Arguments arrow {Obj Arr ArrEq AC} /.
Arguments sub {Obj Arr Sub ASC } /.
Arguments subarr {Obj Arr Sub ASC } /.

Module SubNotations.
  Notation " A '[⇒]' B " := (sub A B) (at level 100, no associativity) : type_scope.
  Notation " A '[→]' B " := (subarr A B) (at level 100, no associativity) : type_scope.
End SubNotations.
Notation " f '̂' " := (subst_of_arr f%bind) (at level 30) : bind_scope.

(** * Lifting *)
Section Lifting.
  Context {Obj : Type}.

  Class LiftableCore (Arr : Obj → Obj → Type) (G : Obj → Obj) :=
    lift : ∀ {A B}, Arr A B → Arr (G A) (G B).

  Notation " f ↑ " := (lift f%bind) (at level 30) : bind_scope.

  Fixpoint liftn {Arr G} {LC : LiftableCore Arr G} {A B : Obj}
           n (f : Arr A B) : Arr (Nat.iter n G A) (Nat.iter n G B) :=
    match n with
    | O => f
    | S n => (liftn n f) ↑
    end.

  Class Liftable {Arr} {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}
        (G : Obj → Obj) {LC : LiftableCore Arr G} : Prop :=
    { lift_id {A} (f : Arr A A) (EQ : f ≡ ı) : f ↑ ≡ ı;
      lift_comp {A B C} (f : Arr B C) (g : Arr A B) h (EQ : f ∘ g ≡ h) :
        f ↑ ∘ g ↑ ≡ h ↑ ;
      lift_proper A B :> Proper (equal A B ==> equal (G A) (G B)) lift
    }.

  Context {Arr : Obj → Obj → Type} {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}.
  Context {Sub : Obj → Obj → Type} {EqSub : EqIndCore Sub} {SC : ArrowCore Sub}.
  Context {ASC : SubstCore Arr Sub}.

  Class ASLiftInj (G : Obj → Obj) {ALC : LiftableCore Arr G} {SLC : LiftableCore Sub G} : Prop :=
    lift_of : ∀ {A B} (f : Arr A B) g (EQ : f ̂ ≡ g), f ↑ ̂ ≡ g ↑.

  Class ASLiftComm (G : Obj → Obj)
        {ALC : LiftableCore Arr G} {SLC : LiftableCore Sub G} : Prop :=
    lift_comm : ∀ {A B₁ B₂ C} (f₁ : Arr B₁ C) (f₂ : Arr A B₂) (g₁ : Sub A B₁) (g₂ : Sub B₂ C)
                (EQ : g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁),
      g₂ ↑ ∘ f₂ ↑ ̂ ≡ f₁ ↑ ̂ ∘ g₁ ↑ .

End Lifting.

Arguments Liftable {Obj} Arr {EqArr AC} G {LC}.
Arguments ASLiftInj {Obj} Arr Sub {EqSub ASC} G {ALC SLC}.
Arguments ASLiftComm {Obj} Arr Sub {EqSub SC ASC} G {ALC SLC}.

Notation " f ↑ " := (lift f%bind) (at level 30) : bind_scope.

(** * Shifting *)
Section Shifting.
  Context {Obj : Type}.

  Class ShiftableCore (Arr : Obj → Obj → Type) (Inc : Obj → Obj) : Type :=
    mk_shift : ∀ A : Obj, Arr A (Inc A).

  Global Arguments mk_shift {Arr Inc _ A}.

  Definition shift
             {Arr : Obj → Obj → Type}
             {F   : Obj → Type} {MapF : FunctorCore F}
             {Inc : Obj → Obj} {Sh : ShiftableCore Arr Inc}
             {A : Obj}
             (a : F A) : F (Inc A) := fmap mk_shift a.

  (*Fixpoint mk_shiftn
           {Arr : Obj → Obj → Type}
           {F   : Obj → Type} {map} {MapF : FunctorCore (F:=F) (Arr:=Arr) map}
           {Inc : Obj → Obj} {AC : ArrowCore Arr} {ALC : ALiftableCore Arr Inc} {Sh : ShiftableCore Arr Inc}
           {A : Obj} n : Arr A (Nat.iter n Inc A) :=  
    match n with
    | O    => ı
    | S n' => (liftA (G := Inc) (mk_shiftn (Inc := Inc) n')) ∘ mk_shift
    end.

  Definition shiftn {Arr : Obj → Obj → Type}
             {F   : Obj → Type} {map} {MapF : FunctorCore (F:=F) (Arr:=Arr) map}
             {Inc : Obj → Obj} {AC : ArrowCore Arr} {ALC : ALiftableCore Arr Inc} {Sh : ShiftableCore Arr Inc}
             n {A : Obj} (a : F A) := fmap (mk_shiftn n) a.*)

  Context (Arr : Obj → Obj → Type) {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}.
  Context (Sub : Obj → Obj → Type) {EqSub : EqIndCore Sub} {SC : ArrowCore Sub}.
  Context {ASC : SubstCore Arr Sub}.
  Context (Inc : Obj → Obj) {Sh : ShiftableCore Arr Inc}.

  Class LiftAShift {ALC : LiftableCore Arr Inc} : Prop :=
    liftA_mk_shift_comm : ∀ {A B : Obj} (f : Arr A B),
      f ↑ ∘ mk_shift ≡ mk_shift ∘ f.

  Class LiftSShift {SLC : LiftableCore Sub Inc} : Prop :=
    liftS_mk_shift_comm : ∀ {A B : Obj} (f : Sub A B),
      f ↑ ∘ mk_shift ̂ ≡ mk_shift ̂ ∘ f.

End Shifting.

Arguments liftA_mk_shift_comm {Obj Arr EqArr AC Inc Sh ALC _ A B} f.
Arguments liftS_mk_shift_comm {Obj Arr Sub EqSub SC ASC Inc  Sh SLC _ A B} f.

(** * Substituting *)
Section Substituting.
  Context {Obj : Type}.

  Class SubstitutableCore
        (Sub : Obj → Obj → Type) (F : Obj → Type) (Inc : Obj → Obj) : Type :=
    mk_subst : ∀ {A : Obj} (x : F A), Sub (Inc A) A.

  Definition subst
             {Sub : Obj → Obj → Type}
             {G   : Obj → Type} {BindG : BindCore G}
             {F   : Obj → Type} {Inc : Obj → Obj} {Sb : SubstitutableCore Sub F Inc}
             {A : Obj}
             (a : G (Inc A)) (v : F A) : G A := bind (mk_subst v) a.

  (*
  Fixpoint mk_substV
           {Sub : Obj → Obj → Type} {Arr : Obj → Obj → Type}
           {G   : Obj → Type} {bnd} {BindG : BindCore (F:=G) (Sub:=Sub) bnd}
           {F   : Obj → Type} {Inc : Obj → Obj} {PSC : PreSubstCore Sub} {AC : ArrowCore Arr}
           {SC : SubstCore Arr Sub} {SLC : SLiftableCore Sub Inc} {Sb : SubstitutableCore Sub F Inc}
           {A : Obj} {n} (xs : Vector.t (F A) n) : Sub (Nat.iter n Inc A) A :=
    match xs with
    | Vector.nil _         => η
    | Vector.cons _ x _ xs => (mk_subst (Inc := Inc) x) • (mk_substV (Inc := Inc) xs) ⇑
    end.

  Definition substV
             {Sub : Obj → Obj → Type} {Arr : Obj → Obj → Type} {AC : ArrowCore Arr}
             {G   : Obj → Type} {bnd} {BindG : BindCore (F:=G) (Sub:=Sub) bnd}
             {F   : Obj → Type} {Inc : Obj → Obj} {PSC : PreSubstCore Sub} {SC : SubstCore Arr Sub}
             {SLC : SLiftableCore Sub Inc} {Sb : SubstitutableCore Sub F Inc}
             {A : Obj} {n} (xs : Vector.t (F A) n) (a : G (Nat.iter n Inc A)) : G A :=
    bind (mk_substV xs) a.
   *)
  
  Context (Arr : Obj → Obj → Type) {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}.
  Context (Sub : Obj → Obj → Type) {EqSub : EqIndCore Sub} {SC : ArrowCore Sub}.
  Context {ASC : SubstCore Arr Sub}.
  Context (F : Obj → Type) (Inc : Obj → Obj) {Sb : SubstitutableCore Sub F Inc}.

  Class SubstShift {Sh : ShiftableCore Arr Inc} : Prop :=
    subst_shift_pure : ∀ {A : Obj} (v : F A),
      mk_subst v ∘ mk_shift ̂ ≡ ı.

  Class SubstFMap {MapF : FunctorCore F}
        {ALC : LiftableCore Arr Inc} : Prop :=
    map_mk_subst_comm : ∀ {A B : Obj} (f : Arr A B) (v : F A),
      f ̂ ∘ mk_subst v ≡ mk_subst (fmap f v) ∘ f ↑ ̂.

  Class SubstBind {BndF : BindCore F}
        {SLC : LiftableCore Sub Inc} : Prop :=
    bind_mk_subst_comm : ∀ {A B : Obj} (f : Sub A B) (v : F A),
      f ∘ mk_subst v ≡ mk_subst (bind f v) ∘ f ↑.

End Substituting.

Arguments subst_shift_pure {Obj Arr Sub EqSub SC ASC F Inc Sb Sh _ A} v.
Arguments map_mk_subst_comm {Obj Arr Sub EqSub SC ASC F Inc Sb MapF ALC _ A B} f v.
Arguments bind_mk_subst_comm {Obj Sub EqSub SC F Inc Sb BndF SLC _ A B} f v.
