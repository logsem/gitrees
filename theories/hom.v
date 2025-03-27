(** In this module, we package up IT homomorphism in a sigma type, and
we will use it as a domain for logical relations on continuations *)
From gitrees Require Import gitree.

Open Scope stdpp_scope.

Section hom.
  Context {A : ofe}.
  Context {CA : Cofe A}.
  Context {F : opsInterp}.
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).

  Record HOM_Type : Type :=
    MkHom {
        hom_fun :> IT -> IT;
        hom_is_hom : IT_hom hom_fun;
      }.

  Global Instance HOM_proper (f : HOM_Type) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, hom_is_hom. Qed.
  Local Instance HOM_equiv : Equiv HOM_Type := λ f g, ∀ x, f x ≡ g x.
  Local Instance HOM_dist : Dist HOM_Type := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition HOM_ofe_mixin : OfeMixin HOM_Type.
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k.
      apply equiv_dist; intros n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n m f g ? x ?; eauto using dist_le with si_solver.
  Qed.
  Canonical Structure HOM := Ofe HOM_Type HOM_ofe_mixin.

  Global Instance HOM_hom (κ : HOM) : IT_hom κ.
  Proof. apply (hom_is_hom κ). Qed.

  Definition HOM_id : HOM := MkHom idfun _.

  Lemma HOM_ccompose (f g : HOM) :
    ∀ α, f (g α) = (f ∘ g) α.
  Proof.
    intro; reflexivity.
  Qed.

  Definition HOM_compose (f g : HOM) : HOM := MkHom (f ∘ g) _.

  Lemma HOM_compose_ccompose (f g h : HOM) :
    h = HOM_compose f g ->
    f ∘ g = h.
  Proof. intros ->. done. Qed.

  Definition IFSCtx_HOM `{!SubOfe natO A} α β : HOM := MkHom (λ x, IFSCtx α β x) _.

  Program Definition LET_HOM (f : IT -n> IT) : HOM
    := MkHom (LETCTX f) (LETCTX_Hom f).

  Lemma LET_HOM_eq α (f : IT -n> IT)
    : LET α f ≡ (LET_HOM f) α.
  Proof. reflexivity. Qed.

End hom.
