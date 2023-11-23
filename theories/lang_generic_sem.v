From gitrees Require Import prelude.
From gitrees Require Import gitree.
Require Import List.
Import ListNotations.

Require Import Binding.Lib Binding.Set.
From Equations Require Import Equations.

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

  Global Instance interp_var_proper {S : Set} (v : S) : Proper ((≡) ==> (≡)) (interp_var v).
  Proof. apply ne_proper. apply _. Qed.

  (* TODO: rewrite in normal-human-being style *)
  Program Definition extend_scope {S : Set}  : interp_scope S -n> IT -n> interp_scope (inc S)
    := λne γ μ x, let x' : inc S := x in match x' with | VZ => μ | VS x'' => γ x'' end.
  Next Obligation.
    match goal with
    | H : context G [(inc S)] |- _ => revert H
    end.
    intros [| a]; simpl; solve_proper.
  Qed.
  Next Obligation.
    match goal with
    | H : context G [(inc S)] |- _ => revert H
    end.
    intros [| a]; simpl; solve_proper.
  Qed.

  Program Definition ren_scope {S S'} (δ : S [→] S') (env : interp_scope S')
    : interp_scope S := λne x, env (δ x).

  (* (** scope substituions *) *)
  (* Inductive ssubst : Set → Type := *)
  (* | emp_ssubst : ssubst ∅ *)
  (* | cons_ssubst {S} : ITV → ssubst S → ssubst (inc S) *)
  (* . *)

  (* Equations interp_ssubst {S} (ss : ssubst S) : interp_scope S := *)
  (*   interp_ssubst emp_ssubst := tt; *)
  (*   interp_ssubst (cons_ssubst αv ss) := (IT_of_V αv, interp_ssubst ss). *)

  (* Equations list_of_ssubst {S} (ss : ssubst S) : list ITV := *)
  (*   list_of_ssubst emp_ssubst := []; *)
  (*   list_of_ssubst (cons_ssubst αv ss) := αv::(list_of_ssubst ss). *)

  (* Equations ssubst_split {S1 S2} (αs : ssubst (S1++S2)) : ssubst S1 * ssubst S2 := *)
  (*   ssubst_split (S1:=[]) αs := (emp_ssubst,αs); *)
  (*   ssubst_split (S1:=u::_) (cons_ssubst αv αs) := *)
  (*     (cons_ssubst αv (ssubst_split αs).1, (ssubst_split αs).2). *)
  (* Lemma interp_scope_ssubst_split {S1 S2} (αs : ssubst (S1++S2)) : *)
  (*   interp_scope_split (interp_ssubst αs) ≡ *)
  (*     (interp_ssubst (ssubst_split αs).1, interp_ssubst (ssubst_split αs).2). *)
  (* Proof. *)
  (*   induction S1 as [|u S1]; simpl. *)
  (*   - simp ssubst_split. simpl. *)
  (*     simp interp_ssubst. done. *)
  (*   - dependent elimination αs as [cons_ssubst αv αs]. *)
  (*     simp ssubst_split. simpl. *)
  (*     simp interp_ssubst. repeat f_equiv; eauto; simpl. *)
  (*      + rewrite IHS1//. *)
  (*      + rewrite IHS1//. *)
  (* Qed. *)
End interp.

(* Common definitions and lemmas for Kripke logical relations *)
Section kripke_logrel.
  Variable s : stuckness.

  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context {R} `{!Cofe R}.

  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Context {A:ofe}. (* The type & predicate for the explicit Kripke worlds *)
  Variable (P : A → iProp).
  Context `{!NonExpansive P}.

  Implicit Types α β : IT.
  Implicit Types αv βv : ITV.
  Implicit Types Φ Ψ : ITV -n> iProp.

  Program Definition expr_pred (α : IT) (Φ : ITV -n> iProp) : iProp :=
    (∀ x : A, P x -∗ WP@{rs} α @ s {{ v, ∃ y : A, Φ v ∗ P y }}).
  #[export] Instance expr_pred_ne : NonExpansive2 expr_pred.
  Proof. solve_proper. Qed.
  #[export] Instance expr_pred_proper : Proper ((≡) ==> (≡) ==> (≡)) expr_pred .
  Proof. solve_proper. Qed.

  (* Definition ssubst_valid {ty} (interp_ty : ty → ITV -n> iProp) {S} (Γ : S -> ty) (ss : ssubst S) : iProp := *)
  (*   ([∗ list] τx ∈ zip (list_of_tyctx Γ) (list_of_ssubst (E:=F) ss), *)
  (*     interp_ty (τx.1) (τx.2))%I. *)

  (* Lemma ssubst_valid_nil {ty} (interp_ty : ty → ITV -n> iProp) : *)
  (*   ⊢ ssubst_valid interp_ty empC emp_ssubst. *)
  (* Proof. *)
  (*   unfold ssubst_valid. *)
  (*   by simp list_of_tyctx list_of_ssubst. *)
  (* Qed. *)

  (* Lemma ssubst_valid_cons {ty} (interp_ty : ty → ITV -n> iProp) {S} *)
  (*   (Γ : tyctx ty S) (ss : ssubst S) τ αv : *)
  (*   ssubst_valid interp_ty (consC τ Γ) (cons_ssubst αv ss) *)
  (*   ⊣⊢ interp_ty τ αv ∗ ssubst_valid interp_ty Γ ss. *)
  (* Proof. *)
  (*   unfold ssubst_valid. *)
  (*   by simp list_of_tyctx list_of_ssubst. *)
  (* Qed. *)

  (* Lemma ssubst_valid_app {ty} (interp_ty : ty → ITV -n> iProp) *)
  (*   {S1 S2} (Ω1 : tyctx ty S1) (Ω2 : tyctx ty S2) αs : *)
  (*   ssubst_valid interp_ty (tyctx_app Ω1 Ω2) αs ⊢ *)
  (*    ssubst_valid interp_ty Ω1 (ssubst_split αs).1 *)
  (*  ∗ ssubst_valid interp_ty Ω2 (ssubst_split αs).2. *)
  (* Proof. *)
  (*   iInduction Ω1 as [|τ Ω1] "IH" forall (Ω2); simp tyctx_app ssubst_split. *)
  (*   - simpl. iIntros "$". iApply ssubst_valid_nil. *)
  (*   - iIntros "H". *)
  (*     rewrite {4 5}/ssubst_valid. *)
  (*     simpl in αs. *)
  (*     dependent elimination αs as [cons_ssubst αv αs]. *)
  (*     simp ssubst_split. simpl. *)
  (*     simp list_of_ssubst list_of_tyctx. *)
  (*     simpl. iDestruct "H" as "[$ H]". *)
  (*     by iApply "IH". *)
  (* Qed. *)

  Lemma expr_pred_ret α αv Φ `{!IntoVal α αv} :
    Φ αv ⊢ expr_pred α Φ.
  Proof.
    iIntros "H".
    iIntros (x) "Hx". iApply wp_val.
    eauto with iFrame.
  Qed.

  (* Lemma expr_pred_bind f `{!IT_hom f} α Φ Ψ `{!NonExpansive Φ} : *)
  (*   expr_pred α Ψ ⊢ *)
  (*   (∀ αv, Ψ αv -∗ expr_pred (f (IT_of_V αv)) Φ) -∗ *)
  (*   expr_pred (f α) Φ. *)
  (* Proof. *)
  (*   iIntros "H1 H2". *)
  (*   iIntros (x) "Hx". *)
  (*   iApply wp_bind. *)
  (*   { solve_proper. } *)
  (*   iSpecialize ("H1" with "Hx"). *)
  (*   iApply (wp_wand with "H1"). *)
  (*   iIntros (βv). iDestruct 1 as (y) "[Hb Hy]". *)
  (*   iModIntro. *)
  (*   iApply ("H2" with "Hb Hy"). *)
  (* Qed. *)

  Lemma expr_pred_frame α Φ :
    WP@{rs} α @ s {{ Φ }} ⊢ expr_pred α Φ.
  Proof.
    iIntros "H".
    iIntros (x) "Hx".
    iApply (wp_wand with "H").
    eauto with iFrame.
  Qed.

End kripke_logrel.

(* Arguments expr_pred_bind {_ _ _ _ _ _ _ _ _ _} f {_}. *)
