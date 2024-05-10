From gitrees Require Import gitree lang_generic.
Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope stdpp_scope.

Section hom.
  Context {sz : nat}.
  Context {a : is_ctx_dep}.
  Context {A : ofe}.
  Context {CA : Cofe A}.
  Context {rs : gReifiers a sz}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).

  Definition HOM : ofe := @sigO (IT -n> IT) IT_hom.

  Global Instance HOM_hom (κ : HOM) : IT_hom (`κ).
  Proof.
    apply (proj2_sig κ).
  Qed.

  Program Definition HOM_id : HOM := exist _ idfun _.
  Next Obligation.
    apply _.
  Qed.

  Lemma HOM_ccompose (f g : HOM) :
    ∀ α, `f (`g α) = (`f ◎ `g) α.
  Proof.
    intro; reflexivity.
  Qed.

  Program Definition HOM_compose (f g : HOM) : HOM := exist _ (`f ◎ `g) _.
  Next Obligation.
    intros f g; simpl.
    apply _.
  Qed.

  Lemma HOM_compose_ccompose (f g h : HOM) :
    h = HOM_compose f g ->
    `f ◎ `g = `h.
  Proof. intros ->. done. Qed.

  Program Definition IFSCtx_HOM `{!SubOfe natO A} α β : HOM := exist _ (λne x, IFSCtx α β x) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.
End hom.
