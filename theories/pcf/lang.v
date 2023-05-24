(** In this file we define the syntax and operational semantics of
PCF. We use a well-typed & well-scoped reprensetation, following the
approach of (Benton, Hur, Kennedy, McBride, JAR 2012) *)
From stdpp Require Import base tactics.
From gitrees Require Import prelude.
From Equations Require Import Equations.
Require Import List.
Import ListNotations.

(** XXX: We /NEED/ this line for [Equations Derive] to work,
 this flag is globally unset by std++, but Equations need obligations to be transparent. *)
Set Transparent Obligations.

Derive NoConfusion NoConfusionHom for list.

(** * Basic PCF syntax *)

Inductive ty :=
| tnat
| tarr (t1 t2 : ty)
.
Derive NoConfusion EqDec for ty.

Definition ctx := (list ty).

(** Variables in a context *)
Inductive var : list ty → ty → Type :=
| Vz : forall {Γ : ctx} {τ}, var (τ::Γ) τ
| Vs : forall {Γ : ctx} {τ τ2 : ty}, var Γ τ -> var (τ2::Γ) τ
.
Derive Signature NoConfusion for var.


(** Well-typed terms in a context *)
Inductive tm : ctx -> ty -> Set :=
| Num : forall {Γ : ctx}, nat -> tm Γ tnat
| Var : forall {Γ : ctx} {τ : ty}, var Γ τ -> tm Γ τ
| Lam : forall {Γ : ctx} {τ1 τ2 : ty}, tm (τ1::Γ) τ2 -> tm Γ (tarr τ1 τ2)
| App : forall {Γ : ctx} {τ1 τ2 : ty}, tm Γ (tarr τ1 τ2) -> tm Γ τ1 -> tm Γ τ2
| Succ : forall {Γ : ctx}, tm Γ tnat -> tm Γ tnat
| Pred : forall {Γ : ctx}, tm Γ tnat -> tm Γ tnat
| Y : forall {Γ : ctx} {τ : ty}, tm Γ (tarr τ τ) -> tm Γ τ
.
Derive Signature NoConfusion NoConfusionHom for tm.

Notation "f · t" := (App f t) (at level 21, left associativity).

(** Substitutions and renamings *)
Definition rens Γ Γ' := ∀ τ, var Γ τ → var Γ' τ.
Definition subs Γ Γ' := ∀ τ, var Γ τ → tm Γ' τ.

Definition idren {Γ} : rens Γ Γ := fun _ v => v.
Definition idsub {Γ} : subs Γ Γ := fun _ => Var.

Equations conssub {Γ Γ' τ} (M : tm Γ' τ) (s : subs Γ Γ') : subs (τ::Γ) Γ' :=
  conssub M s _ Vz := M;
  conssub M s _ (Vs v) := s _ v.

Notation "{| e ; .. ; f |}" := (conssub e .. (conssub f idsub) ..).

Definition tl_sub {Γ Γ' τ} : subs (τ::Γ) Γ' → subs Γ Γ' := λ s τ' v, s _ (Vs v).
Definition hd_sub {Γ Γ' τ} : subs (τ::Γ) Γ' → tm Γ' τ := λ s, s _ Vz.
Definition tl_ren {Γ Γ' τ} : rens (τ::Γ) Γ' → rens Γ Γ' := λ s τ' v, s _ (Vs v).
Definition hd_ren {Γ Γ' τ} : rens (τ::Γ) Γ' → var Γ' τ := λ s, s _ Vz.

(* Lifting a renaming, renaming terms, and lifting substitutions *)
Equations rens_lift {Γ Γ' τ} (s : rens Γ Γ') : rens (τ::Γ) (τ::Γ') :=
  rens_lift s _ Vz := Vz;
  rens_lift s _ (Vs v) := Vs $ s _ v.

Equations ren_tm {Γ Γ' τ} (M : tm Γ τ) (r : rens Γ Γ') : tm Γ' τ :=
ren_tm (Var v) r := Var (r _ v);
ren_tm (Num n) _ := Num n;
ren_tm (App M N) r := App (ren_tm M r) (ren_tm N r);
ren_tm (Succ M) r := Succ $ ren_tm M r;
ren_tm (Pred M) r := Pred $ ren_tm M r;
ren_tm (Y M) r := Y $ ren_tm M r;
ren_tm (Lam M) r := Lam (ren_tm M (rens_lift r)).

Definition tm_lift {Γ τ τ'} (M : tm Γ τ) : tm (τ'::Γ) τ := ren_tm M (λ _ v, Vs v).

Equations subs_lift {Γ Γ' τ} (s : subs Γ Γ') : subs (τ::Γ) (τ::Γ') :=
  subs_lift s _ Vz := Var Vz;
  subs_lift s _ (Vs v) := tm_lift $ s _ v.

(* We can now define the substitution operation *)
Equations subst_tm {Γ Γ' τ} (M : tm Γ τ) (s : subs Γ Γ') : tm Γ' τ :=
subst_tm (Var v) s := s _ v;
subst_tm (Num n) s := Num n;
subst_tm (App M N) s := App (subst_tm M s) (subst_tm N s);
subst_tm (Succ M) s := Succ $ subst_tm M s;
subst_tm (Pred M) s := Pred $ subst_tm M s;
subst_tm (Y M) s := Y $ subst_tm M s;
subst_tm (Lam M) s := Lam (subst_tm M (subs_lift s)).

Definition subst1 {Γ : ctx} {σ τ : ty} (M : tm (σ::Γ) τ) (N : tm Γ σ) : tm Γ τ
  := subst_tm M {| N |}.

Definition comp_r {Γ1 Γ2 Γ3 : ctx} (r1 : rens Γ1 Γ2) (r2 : rens Γ2 Γ3) :
  rens Γ1 Γ3 := λ τ' v, r2 _ (r1 _ v).
Definition comp_r_s {Γ1 Γ2 Γ3 : ctx} (r1 : rens Γ1 Γ2) (s2 : subs Γ2 Γ3) :
  subs Γ1 Γ3 := λ τ' v, s2 _ (r1 _ v).
Definition comp_s_r {Γ1 Γ2 Γ3 : ctx} (s1 : subs Γ1 Γ2) (r2 : rens Γ2 Γ3) :
  subs Γ1 Γ3 := λ τ' v, ren_tm (s1 _ v) r2.
Definition comp_s {Γ1 Γ2 Γ3 : ctx} (s1 : subs Γ1 Γ2) (s2 : subs Γ2 Γ3) :
  subs Γ1 Γ3 := λ τ' v, subst_tm (s1 _ v) s2.


Global Instance rens_equiv Γ Γ' : Equiv (rens Γ Γ') := λ s1 s2, ∀ τ v, s1 τ v = s2 τ v.
Global Instance subs_equiv Γ Γ' : Equiv (subs Γ Γ') := λ s1 s2, ∀ τ v, s1 τ v = s2 τ v.


(** * Semantics *)
(** ** "Typed" reductions counting the number of unfoldings of the Y combinator *)

(** small-step semantics *)
Inductive step : forall {Γ : ctx} {τ : ty}, tm Γ τ → nat → tm Γ τ → Prop :=
| step_app {Γ τ1 τ2} :
    forall (M : tm (τ1::Γ) τ2)
           (N : tm Γ τ1),
     step ((Lam M) · N) 0 (subst1 M N)
| step_unfold {Γ τ} :
    forall (M : tm Γ (tarr τ τ)),
      step (Y M) 1 (M · (Y M))
| step_pred_num {Γ : ctx} n : step (Γ:=Γ) (Pred (Num n)) 0 (Num (pred n))
| step_pred_ctx {Γ : ctx} (M N : tm Γ tnat) k :
    step M k N →
    step (Pred M) k (Pred N)
| step_succ_num {Γ : ctx} n : step (Γ:=Γ) (Succ (Num n)) 0 (Num (S n))
| step_succ_ctx {Γ : ctx} (M N : tm Γ tnat) k :
    step M k N →
    step (Succ M) k (Succ N)
| step_app_right {Γ : ctx} (τ1 τ2 : ty) (M M' : tm Γ (tarr τ1 τ2)) k N :
    step M k M' →
    step (M · N) k (M' · N)
.

Inductive step_clos {Γ : ctx} {τ : ty} : tm  Γ τ → nat → tm Γ τ → Prop :=
| step_clos_none N : step_clos N 0 N
| step_clos_pls N M M' k l :
    step M k M' →
    step_clos M' l N →
    step_clos M (k+l) N
.

(** ** "Untyped" reductions counting the number of beta-reductions *)
(* small-step counting the number of beta reductions *)
Inductive step_beta : forall {Γ : ctx} {τ : ty},
    tm Γ τ → nat → tm Γ τ → Prop :=
| step_beta_app {Γ τ1 τ2} :
    forall (M : tm (τ1::Γ) τ2)
           (N : tm Γ τ1),
     step_beta ((Lam M) · N) 1 (subst1 M N)
| step_beta_unfold {Γ τ} :
    forall (M : tm Γ (tarr τ τ)),
     step_beta (Y M) 0 (M · (Y M))
| step_beta_pred_num {Γ : ctx} n :
     step_beta (Γ:=Γ) (Pred (Num n)) 0  (Num (pred n))
| step_beta_pred_ctx {Γ : ctx} (M N : tm Γ tnat) k :
     step_beta M k N →
     step_beta (Pred M) k (Pred N)
| step_beta_succ_num {Γ : ctx} n :
     step_beta (Γ:=Γ) (Succ (Num n)) 0 (Num (S n))
| step_beta_succ_ctx {Γ : ctx} (M N : tm Γ tnat) k :
     step_beta M k N →
     step_beta (Succ M) k (Succ N)
| step_beta_app_right {Γ : ctx} (τ1 τ2 : ty) (M M' : tm Γ (tarr τ1 τ2)) N  k :
     step_beta M k M' →
     step_beta (M · N) k (M' · N)
.


Inductive step_beta_clos {Γ : ctx} {τ : ty} : tm  Γ τ → nat → tm Γ τ → Prop :=
| step_beta_clos_none N : step_beta_clos N 0 N
| step_beta_clos_pls N M M' k l :
    step_beta M k M' →
    step_beta_clos M' l N →
    step_beta_clos M (k+l) N
.

(** * Contextual equivalence *)

Inductive pctx : ctx -> ty -> ctx -> ty -> Set :=
| EmptyPCtx {Γ τ} : pctx Γ τ Γ τ
| LamPCtx {Γ τ1 τ2 Γ' σ}
  (C : pctx Γ' σ (τ1::Γ) τ2)
 : pctx Γ' σ Γ (tarr τ1 τ2)
| AppLPCtx {Γ τ1 τ2 Γ' σ}
  (C : pctx Γ' σ Γ (tarr τ1 τ2))
  (t2 : tm Γ τ1)
 : pctx Γ' σ Γ τ2
| AppRPCtx {Γ τ1 τ2 Γ' σ}
  (t1 : tm Γ (tarr τ1 τ2))
  (C : pctx Γ' σ Γ τ1)
 : pctx Γ' σ Γ τ2
| SuccPCtx {Γ Γ' σ}
  (C : pctx Γ' σ Γ tnat)
 : (pctx Γ' σ Γ tnat)
| PredPCtx {Γ Γ' σ}
  (C : pctx Γ' σ Γ tnat)
 : (pctx Γ' σ Γ tnat)
| YPCtx {Γ τ Γ' σ}
  (C : pctx Γ' σ Γ (tarr τ τ))
 : (pctx Γ' σ Γ τ)
.
Derive Signature NoConfusion for pctx.

Equations pctx_fill {Γ τ Γ' τ'} (C : pctx Γ τ Γ' τ') (t : tm Γ τ) : tm Γ' τ' :=
  pctx_fill EmptyPCtx t := t;
  pctx_fill (LamPCtx C) t := Lam (pctx_fill C t);
  pctx_fill (AppLPCtx C t2) t := App (pctx_fill C t) t2;
  pctx_fill (AppRPCtx t1 C) t := App t1 (pctx_fill C t);
  pctx_fill (SuccPCtx C) t := Succ (pctx_fill C t);
  pctx_fill (PredPCtx C) t := Pred (pctx_fill C t);
  pctx_fill (YPCtx C) t := Y (pctx_fill C t);
.

Definition ctx_refines {Γ τ} (t1 t2 : tm Γ τ) :=
  ∀ (C : pctx Γ τ [] tnat) k n,
    step_beta_clos (pctx_fill C t1) k (Num n) →
    ∃ k', step_beta_clos (pctx_fill C t2) k' (Num n).

(** * Properties *)

(** ** Properties of renamings and substitutions *)

Ltac simp_all :=
  repeat progress
         (simp subs_lift rens_lift ren_tm subst_tm
          ; simpl).

Global Instance rens_equiv_equivalence Γ Γ' : Equivalence (≡@{rens Γ Γ'}).
Proof.
  split; repeat intro; try naive_solver.
  by rewrite H H0.
Qed.
Global Instance subs_equiv_equivalence Γ Γ' : Equivalence (≡@{subs Γ Γ'}).
Proof.
  split; repeat intro; try naive_solver.
  by rewrite H H0.
Qed.
Global Instance rens_equiv_rewriterelation Γ Γ' : RewriteRelation (≡@{rens Γ Γ'})
  := {}.
Global Instance subs_equiv_rewriterelation Γ Γ' : RewriteRelation (≡@{rens Γ Γ'})
  := {}.


Global Instance rens_lift_proper Γ Γ' τ : Proper ((≡) ==> (≡)) (@rens_lift Γ Γ' τ).
Proof.
  intros r1 r2 Hr. intros τ2 v.
  dependent elimination v; simp_all; try f_equiv; eauto.
Qed.
Global Instance subs_lift_proper Γ Γ' τ : Proper ((≡) ==> (≡)) (@subs_lift Γ Γ' τ).
Proof.
  intros r1 r2 Hr. intros τ2 v.
  dependent elimination v; simp_all; try f_equiv; eauto.
Qed.
Global Instance ren_tm_proper Γ Γ' τ (M : tm Γ τ) : Proper ((≡) ==> (=)) (@ren_tm Γ Γ' _ M).
Proof.
  revert Γ'. induction M =>Γ' r1 r2 Hr; simp_all; try f_equiv; eauto.
  all: try (eapply IHM; try f_equiv; eauto).
  - by eapply IHM1.
  - by eapply IHM2.
Qed.
Global Instance subst_tm_proper Γ Γ' τ (M : tm Γ τ) : Proper ((≡) ==> (=)) (@subst_tm Γ Γ' _ M).
Proof.
  revert Γ'. induction M =>Γ' r1 r2 Hr; simp_all; try f_equiv; eauto.
  all: try (eapply IHM; try f_equiv; eauto).
  - by eapply IHM1.
  - by eapply IHM2.
Qed.

Lemma rens_lift_id {Γ τ} : @rens_lift Γ Γ τ idren ≡ idren.
Proof.
  intros τ' v.
  dependent elimination v; simp subs_lift; simpl; auto.
Qed.
Lemma subs_lift_id {Γ τ} : @subs_lift Γ Γ τ idsub ≡ idsub.
Proof.
  intros τ' v.
  dependent elimination v; simp subs_lift; simpl; auto.
Qed.

Lemma rens_lift_comp_r {Γ D E} (r1 : rens Γ D) (r2 : rens D E) τ :
  @rens_lift _ _ τ (comp_r r1 r2) ≡ comp_r (rens_lift r1) (rens_lift r2).
Proof.
  intros τ' v.
  dependent elimination v; unfold comp_r; simp_all; eauto.
Qed.

Lemma ren_comp_r {Γ D E τ} (M : tm Γ τ) (r1 : rens Γ D) (r2 : rens D E) :
  ren_tm M (comp_r r1 r2) = ren_tm (ren_tm M r1) r2.
Proof.
  revert D E r1 r2. induction M=>D E r1 r2; simp_all; repeat f_equiv; eauto.
  rewrite rens_lift_comp_r. apply IHM.
Qed.

Lemma subs_lift_comp_r_s {Γ D E} (r1 : rens Γ D) (s2 : subs D E) τ :
  @subs_lift _ _ τ (comp_r_s r1 s2) ≡ comp_r_s (rens_lift r1) (subs_lift s2).
Proof.
  intros τ' v.
  dependent elimination v; unfold comp_r_s; simp_all; eauto.
Qed.

Lemma subst_comp_r_s {Γ D E τ} (M : tm Γ τ) (r1 : rens Γ D) (s2 : subs D E) :
  subst_tm M (comp_r_s r1 s2) = subst_tm (ren_tm M r1) s2.
Proof.
  revert D E r1 s2. induction M=>D E r1 s2; simp_all; repeat f_equiv; eauto.
  rewrite subs_lift_comp_r_s. apply IHM.
Qed.

Lemma subs_lift_comp_s_r {Γ D E} (s1 : subs Γ D) (r2 : rens D E) τ :
  @subs_lift _ _ τ (comp_s_r s1 r2) ≡ comp_s_r (subs_lift s1) (rens_lift r2).
Proof.
  intros τ' v.
  dependent elimination v; unfold comp_s_r; simp_all; eauto.
  unfold tm_lift. rewrite -!ren_comp_r. apply ren_tm_proper.
  (* consider this as a sep lemma? *)
  clear.
  intros τ' v.
  dependent elimination v; unfold comp_r; simp_all; eauto.
Qed.

Lemma subst_comp_s_r {Γ D E τ} (M : tm Γ τ) (s1 : subs Γ D) (r2 : rens D E) :
  subst_tm M (comp_s_r s1 r2) = ren_tm (subst_tm M s1) r2.
Proof.
  revert D E s1 r2. induction M=>D E s1 r2; simp_all; repeat f_equiv; eauto.
  rewrite subs_lift_comp_s_r. apply IHM.
Qed.

Lemma subs_lift_comp_s {Γ D E} (s1 : subs Γ D) (s2 : subs D E) τ :
  @subs_lift _ _ τ (comp_s s1 s2) ≡ comp_s (subs_lift s1) (subs_lift s2).
Proof.
  intros τ' v.
  dependent elimination v; unfold comp_s; simp_all; eauto.
  unfold tm_lift. rewrite -subst_comp_r_s -subst_comp_s_r.
  eapply subst_tm_proper.
  (* consider this as a sep lemma? *)
  clear.
  intros τ' v.
  dependent elimination v; unfold comp_s; simp_all; eauto.
Qed.

Lemma subst_comp_s {Γ D E τ} (M : tm Γ τ) (s1 : subs Γ D) (s2 : subs D E) :
  subst_tm M (comp_s s1 s2) = subst_tm (subst_tm M s1) s2.
Proof.
  revert D E s1 s2. induction M=>D E s1 s2; simp_all; repeat f_equiv; eauto.
  rewrite subs_lift_comp_s. apply IHM.
Qed.

Lemma subst_tm_id {Γ τ} (M : tm Γ τ) :
  subst_tm M idsub = M.
Proof.
  induction M; simp_all; repeat f_equiv; eauto.
  rewrite subs_lift_id. apply IHM.
Qed.

(** ** Properties of the small-step semantics *)
Lemma step_det (Γ : ctx) (τ : ty) (M N1 N2 : tm Γ τ) k :
  step M k N1 →
  step M k N2 →
  N1 = N2.
Proof.
  intros Hst. revert N2.
  induction Hst=> N2.
  - intros Hst. dependent elimination Hst.
    + reflexivity.
    + inversion s1.
  - intros Hst. dependent elimination Hst.
    reflexivity.
  - intros Hst. dependent elimination Hst.
    + reflexivity.
    + inversion s.
  - intros Hst2. dependent elimination Hst2.
    + inversion Hst.
    + f_equiv. by apply IHHst.
  - intros Hst. dependent elimination Hst.
    + reflexivity.
    + inversion s0.
  - intros Hst2. dependent elimination Hst2.
    + inversion Hst.
    + f_equiv. by apply IHHst.
  - intros Hst2. dependent elimination Hst2.
    + inversion Hst.
    + f_equiv. by apply IHHst.
Qed.

Lemma step_beta_det (Γ : ctx) (τ : ty) (M N1 N2 : tm Γ τ) k :
  step_beta M k N1 →
  step_beta M k N2 →
  N1 = N2.
Proof.
  intros Hst. revert N2.
  induction Hst=> N2.
  - intros Hst. dependent elimination Hst.
    + reflexivity.
    + inversion s1.
  - intros Hst. dependent elimination Hst.
    reflexivity.
  - intros Hst. dependent elimination Hst.
    + reflexivity.
    + inversion s.
  - intros Hst2. dependent elimination Hst2.
    + inversion Hst.
    + f_equiv. by apply IHHst.
  - intros Hst. dependent elimination Hst.
    + reflexivity.
    + inversion s0.
  - intros Hst2. dependent elimination Hst2.
    + inversion Hst.
    + f_equiv. by apply IHHst.
  - intros Hst2. dependent elimination Hst2.
    + inversion Hst.
    + f_equiv. by apply IHHst.
Qed.

Lemma step_clos_trans {Γ : ctx} {τ : ty} (M1 M2 M3 : tm Γ τ) k k1 k2 :
  step_clos M1 k1 M2 →
  step_clos M2 k2 M3 →
  k = k1 + k2 →
  step_clos M1 k M3.
Proof.
  intros Hcl1. revert k k2 M3.
  induction Hcl1=>n k2 M3.
  - intros ? ->; done.
  - intros HN ->.
    replace (k + l + k2) with (k + (l + k2)) by lia.
    econstructor; eauto.
Qed.

Lemma step_beta_clos_trans {Γ : ctx} {τ : ty} (M1 M2 M3 : tm Γ τ) k k1 k2 :
  step_beta_clos M1 k1 M2 →
  step_beta_clos M2 k2 M3 →
  k = k1 + k2 →
  step_beta_clos M1 k M3.
Proof.
  intros Hcl1. revert k k2 M3.
  induction Hcl1=>n k2 M3.
  - intros ? ->; done.
  - intros HN ->.
    replace (k + l + k2) with (k + (l + k2)) by lia.
    econstructor; eauto.
Qed.

Lemma step_clos_trans_0 {Γ : ctx} {τ : ty} (M1 M2 M3 : tm Γ τ) :
  step_clos M1 0 M2 →
  step_clos M2 0 M3 →
  step_clos M1 0 M3.
Proof. intros. eapply step_clos_trans; eauto. Qed.

Lemma step_clos_once {Γ : ctx} {τ : ty} (M1 M2 : tm Γ τ) k :
  step M1 k M2 →
  step_clos M1 k M2.
Proof.
  intros H1. replace k with (k+0); last lia.
  eapply step_clos_pls; eauto.
  by econstructor.
Qed.

Lemma step_close_Succ {Γ : ctx} (M1 M2 : tm Γ tnat) k :
  step_clos M1 k M2 →
  step_clos (Succ M1) k (Succ M2).
Proof.
  induction 1; econstructor; eauto.
  revert H. clear. intros Hst.
  dependent elimination Hst;
  apply step_succ_ctx; by econstructor.
Qed.

Lemma step_close_Pred {Γ : ctx} (M1 M2 : tm Γ tnat) k :
  step_clos M1 k M2 →
  step_clos (Pred M1) k (Pred M2).
Proof.
  induction 1; econstructor; eauto.
  revert H. clear. intros Hst.
  dependent elimination Hst;
  apply step_pred_ctx; by econstructor.
Qed.

Lemma step_beta_close_Succ {Γ : ctx} (M1 M2 : tm Γ tnat) k :
  step_beta_clos M1 k M2 →
  step_beta_clos (Succ M1) k (Succ M2).
Proof.
  induction 1; econstructor; eauto.
  revert H. clear. intros Hst.
  dependent elimination Hst;
  apply step_beta_succ_ctx; by econstructor.
Qed.

Lemma step_beta_close_Pred {Γ : ctx} (M1 M2 : tm Γ tnat) k :
  step_beta_clos M1 k M2 →
  step_beta_clos (Pred M1) k (Pred M2).
Proof.
  induction 1; econstructor; eauto.
  revert H. clear. intros Hst.
  dependent elimination Hst;
  apply step_beta_pred_ctx; by econstructor.
Qed.


Lemma step_beta_clos_once {Γ : ctx} {τ : ty} (M1 M2 : tm Γ τ) k :
  step_beta M1 k M2 →
  step_beta_clos M1 k M2.
Proof.
  intros H1. replace k with (k+0); last lia.
  repeat econstructor; eauto.
Qed.
