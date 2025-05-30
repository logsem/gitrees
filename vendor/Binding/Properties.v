Require Import Utf8.
Require Import Binding.Core.
Require Import Morphisms.

Section Properties.
  Context {Obj : Type}.
  Context {Arr : Obj → Obj → Type} {EqArr : EqIndCore Arr} {AC : ArrowCore Arr}.
  Context {ArrEq : EqInd Arr} {AA : Arrow Arr}.
  Context {Sub : Obj → Obj → Type} {EqSub : EqIndCore Sub} {SC : ArrowCore Sub}.
  Context {ASC : SubstCore Arr Sub} {SubEq : EqInd Sub} {AS : Arrow Sub} {SS : Subst Arr Sub}.
  Context {F G : Obj → Type}.
  Context {Inc : Obj → Obj}.
  Context {Sh  : ShiftableCore Arr Inc}.
  Context {ALC : LiftableCore Arr Inc}.
  Context {SLC : LiftableCore Sub Inc}.
  Context {Sb : SubstitutableCore Sub F Inc}.
  Context {LAS : LiftAShift Arr Inc}.
  Context {LSS : LiftSShift Arr Sub Inc}.
  Context {MapF : FunctorCore (Arr := Arr) F}.
  Context {MapG : FunctorCore (Arr := Arr) G}
          {MG : Functor G}.
  Context {BindF : BindCore (Sub := Sub) F}.
  Context {BindG : BindCore (Sub := Sub) G}
          {BMPG : BindMapPure G} {BMCG : BindMapComm G} {BG : Bind G}.
  Context {SbShF  : SubstShift Arr Sub F Inc}.
  Context {SbMapF : SubstFMap  Arr Sub F Inc}.
  Context {SbBndF : SubstBind  Sub F Inc}.
  Context {AL     : Liftable Arr Inc}.
  Context {SL     : Liftable Sub Inc}.
  Context {ASLI   : ASLiftInj Arr Sub Inc} {ASLC : ASLiftComm Arr Sub Inc}.


  Local Open Scope bind_scope.

  Lemma map_id' {A : Obj} (t : G A) :
    fmap ı t = t.
  Proof.
    apply map_id; reflexivity.
  Qed.

  Lemma map_map_comp' {A B C : Obj} (f : Arr B C) (g : Arr A B) (t : G A) :
    fmap f (fmap g t) = fmap (f ∘ g) t.
  Proof.
    apply map_map_comp; reflexivity.
  Qed.

  Global Instance fmap_proper A B : Proper (equal A B ==> eq ==> eq) fmap.
  Proof.
    intros f g EQ t t' EQ'; subst t'.
    erewrite <- map_id', map_map_comp; [reflexivity |].
    rewrite arrow_comp_id_l, EQ; reflexivity.
  Qed.

  Lemma bind_pure' {A : Obj} (t : G A) :
    bind ı t = t.
  Proof.
    apply bind_pure; reflexivity.
  Qed.

  Lemma bind_bind_comp' {A B C : Obj} (f : Sub B C) (g : Sub A B) (t : G A) :
    bind f (bind g t) = bind (f ∘ g) t.
  Proof.
    apply bind_bind_comp; reflexivity.
  Qed.

  Global Instance bind_proper A B : Proper (equal A B ==> eq ==> eq) bind.
  Proof.
    intros f g EQ t t' EQ'; subst t'.
    erewrite <- bind_pure', bind_bind_comp; [reflexivity |].
    now rewrite EQ, arrow_comp_id_l.
  Qed.

  Lemma map_to_bind {A B : Obj} (f : Arr A B) (t : G A) :
    fmap f t = bind (f ̂) t.
  Proof.
    now apply bind_map.
  Qed.

  Lemma fmap_liftA_shift_comm {A B : Obj} (f : Arr A B) (t : G A) :
    fmap (f ↑) (shift t) = shift (fmap f t).
  Proof.
    unfold shift; now rewrite !map_map_comp', liftA_mk_shift_comm.
  Qed.

  Lemma bind_liftS_shift_comm {A B : Obj} (f : Sub A B) (a : G A) :
    bind (f ↑) (shift a) = shift (bind f a).
  Proof.
    unfold shift; apply bind_map_comm, liftS_mk_shift_comm.
  Qed.

  Lemma bind_map_id {A B : Obj} (g : Sub B A) (f : Arr A B) (a : G A)
        (EQ : g ∘ f ̂ ≡ ı) :
    bind g (fmap f a) = a.
  Proof.
    rewrite bind_map_comm with (f₁ := ı) (g₁ := ı), map_id', bind_pure'; [reflexivity |].
    now rewrite EQ, arrow_comp_id_r, arrow_subst_id.
  Qed.

  Lemma subst_shift_id {A : Obj} (t : G A) (v : F A):
    subst (shift t) v = t.
  Proof.
    unfold shift, subst; apply bind_map_id, subst_shift_pure.
  Qed.

  Lemma lift_of_arrow {A B : Obj} (δ : Arr A B) :
    δ ↑ ̂ ≡ δ ̂ ↑.
  Proof.
    now apply lift_of.
  Qed.

  Lemma subst_shift_id_lifted {A : Obj} (t : G (Inc A)) (v : F A) :
    bind (mk_subst v ↑) (fmap (mk_shift ↑) t) = t.
  Proof.
    apply bind_map_id; rewrite lift_of_arrow, lift_comp by reflexivity.
    apply lift_id, subst_shift_pure.
  Qed.

  Lemma subst_shift_id_lifted2 {A : Obj} (t : G (Inc (Inc A))) (v : F A) :
    bind ((mk_subst v) ↑ ↑) (fmap (mk_shift ↑ ↑) t) = t.
  Proof.
    apply bind_map_id; rewrite lift_of_arrow, lift_comp by reflexivity.
    apply lift_id; rewrite lift_of_arrow, lift_comp by reflexivity.
    apply lift_id, subst_shift_pure.
  Qed.

  Lemma fmap_subst {A B : Obj} (f : Arr A B) (t : G (Inc A)) (v : F A) :
    fmap f (subst t v) = subst (fmap (f ↑) t) (fmap f v).
  Proof.
    unfold subst; symmetry; erewrite bind_map_comm; [reflexivity |].
    symmetry; apply map_mk_subst_comm.
  Qed.

  Lemma shift_subst {Inc' : Obj → Obj} {Sh' : ShiftableCore Arr Inc'}
        {A : Obj} (t : G (Inc A)) (v : F A) :
    shift (subst t v) = subst (fmap (mk_shift ↑) t) (shift v).
  Proof.
    apply fmap_subst.
  Qed.

  Lemma bind_subst {A B : Obj} (f : Sub A B) (t : G (Inc A)) (v : F A) :
    bind f (subst t v) = subst (bind (f ↑) t) (bind f v).
  Proof.
    unfold subst; now rewrite !bind_bind_comp', bind_mk_subst_comm.
  Qed.

End Properties.
