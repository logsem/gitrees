From gitrees Require Import prelude.
From gitrees Require Import gitree.
Require Import List.
Import ListNotations.

Require Import Binding.Lib Binding.Set.

Section interp.
  Local Open Scope type.
  Context {E: opsInterp}.
  Context {R} `{!Cofe R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Definition interp_scope (S : Set) : ofe := (leibnizO S) -n> IT.

  Global Instance interp_scope_cofe S : Cofe (interp_scope S).
  Proof. apply _. Qed.

  Global Instance interp_scope_inhab S : Inhabited (interp_scope S).
  Proof. apply _. Defined.

  Program Definition interp_var {S : Set} (v : S) : interp_scope S -n> IT :=
    λne (f : interp_scope S), f v.
  Next Obligation.
    solve_proper.
  Qed.

  Global Instance interp_var_proper {S : Set} (v : S) : Proper ((≡) ==> (≡)) (interp_var v).
  Proof. apply ne_proper. apply _. Qed.

  Program Definition extend_scope {S : Set}  : interp_scope S -n> IT -n> interp_scope (inc S)
    := λne γ μ x, let x' : inc S := x in
                  match x' with
                  | VZ => μ
                  | VS x'' => γ x''
                  end.
  Next Obligation.
    intros ???? [| x] [| y]; term_simpl; [solve_proper | inversion 1 | inversion 1 | inversion 1; by subst].
  Qed.
  Next Obligation.
    intros ??????.
    intros [| a]; term_simpl; solve_proper.
  Qed.
  Next Obligation.
    intros ??????.
    intros [| a]; term_simpl; solve_proper.
  Qed.

  Program Definition ren_scope {S S'} (δ : S [→] S') (env : interp_scope S')
    : interp_scope S := λne x, env (δ x).

End interp.

(* Common definitions and lemmas for Kripke logical relations *)
Section kripke_logrel.
  Variable s : stuckness.

  Context {sz : nat} {a : is_ctx_dep}.
  Variable rs : gReifiers a sz.
  Context {R} `{!Cofe R}.

  Notation F := (gReifiers_ops a rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Context {A:ofe}. (* The type & predicate for the explicit Kripke worlds *)
  Variable (P : A -n> iProp).

  Implicit Types α β : IT.
  Implicit Types αv βv : ITV.
  Implicit Types Φ Ψ : ITV -n> iProp.

  Program Definition expr_pred (α : IT) (Φ : ITV -n> iProp) : iProp :=
    (∀ x : A, P x -∗ wp rs α s ⊤ (λne v, ∃ y : A, Φ v ∗ P y)).
  Next Obligation.
    solve_proper.
  Qed.

  Global Instance expr_pred_ne {n} : Proper (dist n ==> dist n ==> dist n) expr_pred.
  Proof.
    solve_proper.
  Qed.

  Global Instance expr_pred_proper : Proper (equiv ==> equiv ==> equiv) expr_pred.
  Proof.
    solve_proper.
  Qed.

  Lemma expr_pred_ret α αv Φ `{!IntoVal α αv} :
    Φ αv ⊢ expr_pred α Φ.
  Proof.
    iIntros "H".
    iIntros (x) "Hx". iApply wp_val.
    simpl.
    iExists x.
    by iFrame.
  Qed.

  Lemma expr_pred_frame α Φ :
    WP@{rs} α @ s {{ Φ }} ⊢ expr_pred α Φ.
  Proof.
    iIntros "H".
    iIntros (x) "Hx".
    iApply (wp_wand with "H").
    simpl.
    iIntros (v) "Hv".
    iExists x.
    by iFrame.
  Qed.

End kripke_logrel.

Section kripke_logrel_ctx_indep.
  Variable s : stuckness.

  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context {R} `{!Cofe R}.

  Notation F := (gReifiers_ops NotCtxDep rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Context {A : ofe}.
  Variable (P : A -n> iProp).

  Implicit Types α β : IT.
  Implicit Types αv βv : ITV.
  Implicit Types Φ Ψ : ITV -n> iProp.

  Local Notation expr_pred := (expr_pred s rs P).

  Lemma expr_pred_bind f `{!IT_hom f} α Φ Ψ `{!NonExpansive Φ}
    : expr_pred α Ψ ⊢
      (∀ αv, Ψ αv -∗ expr_pred (f (IT_of_V αv)) Φ)
      -∗ expr_pred (f α) Φ.
  Proof.
    iIntros "H1 H2".
    iIntros (x) "Hx".
    iApply wp_bind.
    iSpecialize ("H1" with "Hx").
    iApply (wp_wand with "H1").
    iIntros (βv). iDestruct 1 as (y) "[Hb Hy]".
    iModIntro.
    iApply ("H2" with "Hb Hy").
  Qed.
End kripke_logrel_ctx_indep.

Arguments expr_pred_bind {_ _ _ _ _ _ _ _ _ _} f {_ _}.
