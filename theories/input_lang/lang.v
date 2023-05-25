(** A simple language with recursion and a single INPUT effect *)
From stdpp Require Export strings.
From gitrees Require Import prelude.
From Equations Require Import Equations.
Require Import List.
Import ListNotations.

(** XXX: We /NEED/ this line for [Equations Derive] to work,
 this flag is globally unset by std++, but Equations need obligations to be transparent. *)
Set Transparent Obligations.

Derive NoConfusion NoConfusionHom for list.

Definition scope := (list unit).

(** Variables in a context *)
Inductive var : scope → Type :=
| Vz : forall {S : scope} {s}, var (s::S)
| Vs : forall {S : scope} {s}, var S -> var (s::S)
.
Derive Signature NoConfusion for var.

Delimit Scope expr_scope with E.

Inductive nat_op := Add | Sub.

Inductive expr : scope → Type :=
  (* Values *)
  | Val : forall {S}, val S → expr S
  (* Base lambda calculus *)
  | Var : forall {S}, var S            → expr S
  | Rec : forall {S}, expr (()::()::S) → expr S
  | App : forall {S}, expr S → expr S  → expr S
  (* Base types and their operations *)
  | NatOp : forall {S},
      nat_op → expr S → expr S         → expr S
  | If : forall {S},
    expr S → expr S → expr S           → expr S
  (* The input effect *)
  | Input : forall {S},                  expr S
with val : scope → Type :=
  | Lit : forall {S}, nat               → val S
  | RecV : forall {S}, expr (()::()::S) → val S.

Bind Scope expr_scope with expr.
Notation of_val := Val (only parsing).

Definition to_val {S} (e : expr S) : option (val S) :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition nat_op_interp {S} (n : nat_op) (x y : val S) : option (val S) :=
  match x, y with
  | Lit x, Lit y =>
      match n with
      | Add => Some $ Lit $ x+y
      | Sub => Some $ Lit $ x-y
      end
  | _,_ => None
  end.

(** substitution stuff *)
Definition rens S S' := var S → var S'.
Definition subs S S' := var S → expr S'.

Definition idren {S} : rens S S := fun v => v.
Definition idsub {S} : subs S S := Var.

Equations conssub {S S' τ} (M : expr S') (s : subs S S') : subs (τ::S) S' :=
  conssub M s Vz := M;
  conssub M s (Vs v) := s v.

Notation "{/ e ; .. ; f /}" := (conssub e .. (conssub f idsub) ..).

Definition tl_sub {S S' τ} : subs (τ::S) S' → subs S S' := λ s v, s (Vs v).
Definition hd_sub {S S' τ} : subs (τ::S) S' → expr S' := λ s, s Vz.
Definition tl_ren {S S' τ} : rens (τ::S) S' → rens S S' := λ s v, s (Vs v).
Definition hd_ren {S S' τ} : rens (τ::S) S' → var S' := λ s, s Vz.

(* Lifting a renaming, renaming terms, and lifting substitutions *)
Equations rens_lift {S S'} (s : rens S S') : rens (()::S) (()::S') :=
  rens_lift s Vz := Vz;
  rens_lift s (Vs v) := Vs $ s v.

Equations ren_expr {S S'} (M : expr S) (r : rens S S') : expr S' :=
ren_expr (Val v) r := Val $ ren_val v r;
ren_expr (Var v) r := Var (r v);
ren_expr (Rec M) r := Rec (ren_expr M (rens_lift (rens_lift r)));
ren_expr (App M N) r := App (ren_expr M r) (ren_expr N r);
ren_expr (NatOp op e1 e2) r := NatOp op (ren_expr e1 r) (ren_expr e2 r);
ren_expr (If e0 e1 e2) r := If (ren_expr e0 r) (ren_expr e1 r) (ren_expr e2 r);
ren_expr Input r := Input;
with ren_val {S S'} (M : val S) (r : rens S S') : val S' :=
ren_val (Lit n) _ := Lit n;
ren_val (RecV e) r := RecV (ren_expr e (rens_lift (rens_lift r))).


Definition expr_lift {S} (M : expr S) : expr (()::S) := ren_expr M Vs.

Equations subs_lift {S S'} (s : subs S S') : subs (()::S) (()::S') :=
  subs_lift s Vz := Var Vz;
  subs_lift s (Vs v) := expr_lift $ s v.

(* We can now define the substitution operation *)
Equations subst_expr {S S'} (M : expr S) (s : subs S S') : expr S' :=
subst_expr (Val v) r := Val $ subst_val v r;
subst_expr (Var v) r := r v;
subst_expr (Rec M) r := Rec (subst_expr M (subs_lift (subs_lift r)));
subst_expr (App M N) r := App (subst_expr M r) (subst_expr N r);
subst_expr (NatOp op e1 e2) r := NatOp op (subst_expr e1 r) (subst_expr e2 r);
subst_expr (If e0 e1 e2) r := If (subst_expr e0 r) (subst_expr e1 r) (subst_expr e2 r);
subst_expr (Input) r := Input;
with subst_val {S S'} (M : val S) (r : subs S S') : val S' :=
subst_val (Lit n) _ := Lit n;
subst_val (RecV e) r := RecV (subst_expr e (subs_lift (subs_lift r))).

Definition subst1 {S : scope} {τ} (M : expr (τ::S)) (N : expr S) : expr S
  := subst_expr M {/ N /}.
Definition subst2 {S : scope} {i j} (M : expr (i::j::S)) (N1 : expr S) (N2 : expr S) : expr S
  := subst_expr M {/ N1; N2 /}.

Definition appsub {S1 S2 S3} (s : subs S1 S2) (s' : subs S2 S3) : subs S1 S3 :=
  λ v, subst_expr (s v) s'.

Global Instance rens_equiv S S' : Equiv (rens S S') := λ s1 s2, ∀ v, s1 v = s2 v.
Global Instance subs_equiv S S' : Equiv (subs S S') := λ s1 s2, ∀ v, s1 v = s2 v.

Global Instance rens_lift_proper S S' : Proper ((≡) ==> (≡)) (@rens_lift S S').
Proof.
  intros s1 s2 Hs v. dependent elimination v; simp rens_lift; eauto.
  f_equiv. apply Hs.
Qed.

Lemma ren_expr_proper {S S'} (e : expr S) : Proper ((≡) ==> (=)) (@ren_expr S S' e)
  with ren_val_proper  {S S'} v : Proper ((≡) ==> (=)) (@ren_val S S' v).
Proof.
  - revert S'.
    induction e; intros S' s1 s2 Hs; simp ren_expr;
      f_equiv; try solve [eauto | apply ren_expr_proper; eauto ].
    + by apply ren_val_proper.
    + apply ren_expr_proper. by repeat f_equiv.
  - revert S'.
    induction v; intros S' s1 s2 Hs; simp ren_expr;
      f_equiv; try solve [eauto | apply ren_expr_proper; eauto ].
    apply ren_expr_proper. by repeat f_equiv.
Qed.

#[export] Existing Instance ren_expr_proper.
#[export] Existing Instance ren_val_proper.

#[export]  Instance subs_lift_proper S S' : Proper ((≡) ==> (≡)) (@subs_lift S S').
Proof.
  intros s1 s2 Hs v. dependent elimination v; simp subs_lift; eauto.
  f_equiv. apply Hs.
Qed.

Lemma subst_expr_proper {S S'} (e : expr S) : Proper ((≡) ==> (=)) (@subst_expr S S' e)
  with subst_val_proper  {S S'} v : Proper ((≡) ==> (=)) (@subst_val S S' v).
Proof.
  - revert S'.
    induction e; intros S' s1 s2 Hs; simp subst_expr;
      f_equiv; try solve [eauto | apply subst_expr_proper; eauto ].
    + by apply subst_val_proper.
    + apply subst_expr_proper. by repeat f_equiv.
  - revert S'.
    induction v; intros S' s1 s2 Hs; simp subst_expr;
      f_equiv; try solve [eauto | apply subst_expr_proper; eauto ].
    apply subst_expr_proper. by repeat f_equiv.
Qed.
#[export]  Existing Instance subst_expr_proper.
#[export]  Existing Instance subst_val_proper.

Lemma subst_ren_expr {S1 S2 S3} e (s : subs S2 S3) (r : rens S1 S2) :
  subst_expr (ren_expr e r) s = subst_expr e (compose s r)
with subst_ren_val  {S1 S2 S3} v (s : subs S2 S3) (r : rens S1 S2) :
  subst_val (ren_val v r) s = subst_val v (compose s r).
Proof.
  - revert S2 S3 r s.
    induction e=>S2 S3 r s; simp ren_expr; simp subst_expr; try f_equiv; eauto.
    rewrite IHe. apply subst_expr_proper.
    intro v. simpl.
    dependent elimination v; simp rens_lift; simp subs_lift; eauto.
    f_equiv. dependent elimination v; simp rens_lift; simp subs_lift; eauto.
  - revert S2 S3 r s.
    induction v=>S2 S3 r s; simpl; simp ren_val; simp subst_val; try f_equiv.
    rewrite subst_ren_expr.
    apply subst_expr_proper.
    intro v. simpl.
    dependent elimination v; simp rens_lift; simp subs_lift; eauto.
    f_equiv. dependent elimination v; simp rens_lift; simp subs_lift; eauto.
Qed.

Lemma ren_ren_expr {S1 S2 S3} e (s : rens S2 S3) (r : rens S1 S2) :
  ren_expr (ren_expr e r) s = ren_expr e (compose s r)
with ren_ren_val  {S1 S2 S3} v (s : rens S2 S3) (r : rens S1 S2) :
  ren_val (ren_val v r) s = ren_val v (compose s r).
Proof.
  - revert S2 S3 r s.
    induction e=>S2 S3 r s; simp ren_expr; try f_equiv; eauto.
    rewrite IHe. apply ren_expr_proper.
    intro v. simpl.
    dependent elimination v; simp rens_lift; simp subs_lift; eauto.
    f_equiv. dependent elimination v; simp rens_lift; simp subs_lift; eauto.
  - revert S2 S3 r s.
    induction v=>S2 S3 r s; simpl; simp ren_val; simp subst_val; try f_equiv.
    rewrite ren_ren_expr.
    apply ren_expr_proper.
    intro v. simpl.
    dependent elimination v; simp rens_lift; simp subs_lift; eauto.
    f_equiv. dependent elimination v; simp rens_lift; simp subs_lift; eauto.
Qed.

Definition rcompose {S1 S2 S3} (r : rens S2 S3) (s : subs S1 S2)  : subs S1 S3 :=
  λ v, ren_expr (s v) r.

Lemma ren_subst_expr {S1 S2 S3} e (s : subs S1 S2) (r : rens S2 S3) :
  ren_expr (subst_expr e s) r = subst_expr e (rcompose r s)
with ren_subst_val {S1 S2 S3} v (s : subs S1 S2) (r : rens S2 S3) :
  ren_val (subst_val v s) r = subst_val v (rcompose r s).
Proof.
  - revert S2 S3 r s.
    induction e=>S2 S3 r s; simp subst_expr; simp ren_expr; try f_equiv; eauto.
    rewrite IHe. apply subst_expr_proper.
    intro v. simpl. unfold rcompose.
    dependent elimination v; eauto.
    dependent elimination v; eauto.
    simp subs_lift. unfold expr_lift.
    rewrite !ren_ren_expr. apply ren_expr_proper.
    intro x. dependent elimination v; eauto.
  - revert S2 S3 r s.
    induction v=>S2 S3 r s; simp subst_expr; simp ren_expr; try f_equiv; eauto.
    rewrite ren_subst_expr. apply subst_expr_proper.
    intro v. simpl. unfold rcompose.
    dependent elimination v; eauto.
    dependent elimination v; eauto.
    simp subs_lift. unfold expr_lift.
    rewrite !ren_ren_expr. apply ren_expr_proper.
    intro x. dependent elimination v; eauto.
Qed.

Lemma appsub_lift {S1 S2 S3} (s : subs S1 S2) (s' : subs S2 S3) :
  subs_lift (appsub s s') ≡ appsub (subs_lift s) (subs_lift s').
Proof.
  unfold appsub.
  intro v. dependent elimination v; simp subs_lift; eauto.
  unfold expr_lift. rewrite subst_ren_expr.
  rewrite ren_subst_expr. apply subst_expr_proper.
  intro x. unfold rcompose. simpl. simp subs_lift. done.
Qed.

Lemma subst_expr_appsub {S1 S2 S3} (s1 : subs S1 S2) (s2 : subs S2 S3) e :
  subst_expr (subst_expr e s1) s2 = subst_expr e (appsub s1 s2)
with subst_val_appsub {S1 S2 S3} (s1 : subs S1 S2) (s2 : subs S2 S3) v :
  subst_val (subst_val v s1) s2 = subst_val v (appsub s1 s2).
Proof.
  - revert S2 S3 s1 s2.
    induction e=>S2 S3 s1 s2; simp subst_expr; try f_equiv; eauto.
    rewrite !appsub_lift. apply IHe.
  - revert S3 s2.
    induction v=>S3 s2; simpl; f_equiv; eauto.
    rewrite !appsub_lift. apply subst_expr_appsub.
Qed.

Lemma subst_expr_lift {S S'} e e1 (s : subs S S') :
  subst_expr (expr_lift e) (conssub e1 s) = subst_expr e s.
Proof.
  unfold expr_lift.
  rewrite subst_ren_expr. apply subst_expr_proper.
   intro v. simpl. simp conssub. done.
Qed.

Lemma subst_expr_idsub {S} (e : expr S) :
  subst_expr e idsub = e
with subst_val_idsub {S} (v : val S) :
  subst_val v idsub = v.
Proof.
  - induction e; simp subst_expr; simpl; try f_equiv; eauto.
    assert ((subs_lift (subs_lift idsub)) ≡ idsub) as ->; last auto.
    intro v.
    dependent elimination v; simp subs_lift; auto.
    dependent elimination v; simp subs_lift; auto.
  - induction v; simp subst_val; simpl; try f_equiv; eauto.
    assert ((subs_lift (subs_lift idsub)) ≡ idsub) as ->; last auto.
    intro v.
    dependent elimination v; simp subs_lift; auto.
    dependent elimination v; simp subs_lift; auto.
Qed.

(*** Operational semantics *)

Record state := State {
                   inputs : list nat;
                 }.
#[export] Instance state_inhabited : Inhabited state := populate (State []).


Definition update_input (s : state) : nat * state :=
  match s.(inputs) with
  | [] => (0, s)
  | n::ns =>
      (n, {| inputs := ns |})
  end.


Inductive head_step {S} : expr S → state → expr S → state → nat*nat → Prop :=
| RecS e σ :
  head_step (Rec e) σ (Val $ RecV e) σ (0,0)
| BetaS e1 v2 e' σ :
  e' = subst2 e1 (Val $ RecV e1) (Val v2) →
  head_step (App (Val $ RecV e1) (Val v2)) σ e' σ (1,0)
| InputS σ n σ' :
  update_input σ = (n,σ') →
  head_step Input σ (Val (Lit n)) σ' (1,1)
| NatOpS op v1 v2 v3 σ :
  nat_op_interp op v1 v2 = Some v3 →
  head_step (NatOp op (Val v1) (Val v2)) σ
            (Val v3) σ (0,0)
| IfTrueS n e1 e2 σ :
  n > 0 →
  head_step (If (Val (Lit n)) e1 e2) σ
            e1 σ (0,0)
| IfFalseS n e1 e2 σ :
  n = 0 →
  head_step (If (Val (Lit n)) e1 e2) σ
            e2 σ (0,0)
.

Lemma head_step_io_01 {S} (e1 e2 : expr S) σ1 σ2 n m :
  head_step e1 σ1 e2 σ2 (n,m) → m = 0 ∨ m = 1.
Proof.  inversion 1; eauto. Qed.
Lemma head_step_unfold_01 {S} (e1 e2 : expr S) σ1 σ2 n m :
  head_step e1 σ1 e2 σ2 (n,m) → n = 0 ∨ n = 1.
Proof.  inversion 1; eauto. Qed.
Lemma head_step_no_io {S} (e1 e2 : expr S) σ1 σ2 n :
  head_step e1 σ1 e2 σ2 (n,0) → σ1 = σ2.
Proof.  inversion 1; eauto. Qed.

Inductive ectx_item {S} :=
  | AppLCtx (v2 : val S)
  | AppRCtx (e1 : expr S)
  | NatOpLCtx (op : nat_op) (v2 : val S)
  | NatOpRCtx (op : nat_op) (e1 : expr S)
  | IfCtx (e1 e2 : expr S)
.
Arguments ectx_item S : clear implicits.

Definition fill_item {S} (Ki : ectx_item S) (e : expr S) : expr S :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | NatOpLCtx op v2 => NatOp op e (Val v2)
  | NatOpRCtx op e1 => NatOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  end.

(** Carbonara from heap lang *)
Global Instance fill_item_inj {S} (Ki : ectx_item S) : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val {S} Ki (e : expr S) :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck {S} (e1 : expr S) σ1 e2 σ2 m : head_step e1 σ1 e2 σ2 m → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_item_step_val {S} Ki (e : expr S) σ1 e2 σ2 m :
  head_step (fill_item Ki e) σ1 e2 σ2 m → is_Some (to_val e).
Proof. revert m e2. induction Ki; simpl; inversion 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj {S} Ki1 Ki2 (e1 e2 : expr S) :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; naive_solver eauto with f_equal.
Qed.

(** Lifting the head step **)

Definition ectx S := (list (ectx_item S)).
Definition fill {S} (K : ectx S) (e : expr S) : expr S := foldl (flip fill_item) e K.

Lemma fill_app {S} (K1 K2 : ectx S) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.


Lemma fill_val : ∀ {S} K (e : expr S), is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof. intros S K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. Qed.

Lemma fill_not_val : ∀ {S} K (e : expr S), to_val e = None → to_val (fill K e) = None.
Proof.
  intros S K e. rewrite !eq_None_not_Some.
  eauto using fill_val.
Qed.

Lemma fill_empty {S} (e : expr S) : fill [] e = e.
Proof. reflexivity. Qed.
Lemma fill_comp {S} K1 K2 (e : expr S) : fill K1 (fill K2 e) = fill (K2 ++ K1) e.
Proof. by rewrite fill_app. Qed.
Global Instance fill_inj {S} (K:ectx S) : Inj (=) (=) (fill K).
Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.


Inductive prim_step {S} (e1 : expr S) (σ1 : state)
          (e2 : expr S) (σ2 : state) (n : nat*nat) : Prop:=
  Ectx_step (K : ectx S) e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 e2' σ2 n → prim_step e1 σ1 e2 σ2 n.

Lemma prim_step_pure {S} (e1 e2 : expr S) σ1 σ2 n :
  prim_step e1 σ1 e2 σ2 (n,0) → σ1 = σ2.
Proof.
  inversion 1; simplify_eq/=.
  inversion H2; eauto.
Qed.

Inductive prim_steps {S} : expr S → state → expr S → state → nat*nat → Prop :=
| prim_steps_zero e σ :
  prim_steps e σ e σ (0,0)
| prim_steps_abit e1 σ1 e2 σ2 e3 σ3 n1 m1 n2 m2 :
  prim_step e1 σ1 e2 σ2 (n1,m1) →
  prim_steps e2 σ2 e3 σ3 (n2,m2) →
  prim_steps e1 σ1 e3 σ3 (n1+n2,m1+m2)
.

Lemma Ectx_step' {S} (K : ectx S) e1 σ1 e2 σ2 efs :
  head_step e1 σ1 e2 σ2 efs → prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
Proof. econstructor; eauto. Qed.

Lemma prim_step_ctx {S} (K : ectx S) e1 σ1 e2 σ2 efs :
  prim_step e1 σ1 e2 σ2 efs → prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
Proof.
  destruct 1 as [K2 u1 u2 HK2].
  subst e1 e2. rewrite -!fill_app.
  by econstructor; eauto.
Qed.

Lemma prim_steps_ctx {S} (K : ectx S) e1 σ1 e2 σ2 efs :
  prim_steps e1 σ1 e2 σ2 efs → prim_steps (fill K e1) σ1 (fill K e2) σ2 efs.
Proof.
  induction 1; econstructor; eauto using prim_step_ctx.
Qed.

Lemma prim_steps_app {S} nm1 nm2 (e1 e2 e3 : expr S) σ1 σ2 σ3 :
  prim_steps e1 σ1 e2 σ2 nm1 → prim_steps e2 σ2 e3 σ3 nm2 →
  prim_steps e1 σ1 e3 σ3 (nm1.1 + nm2.1, nm1.2 + nm2.2).
Proof.
  intros Hst. revert nm2.
  induction Hst; intros [n' m']; simplify_eq/=; first done.
  rewrite -!Nat.add_assoc. intros Hsts.
  econstructor; eauto.
  by apply (IHHst (n',m')).
Qed.

Lemma prim_step_steps {S} nm (e1 e2 : expr S) σ1 σ2 :
  prim_step e1 σ1 e2 σ2 nm → prim_steps e1 σ1 e2 σ2 nm.
Proof.
  destruct nm as [n m]. intro Hs.
  rewrite -(Nat.add_0_r n).
  rewrite -(Nat.add_0_r m).
  econstructor; eauto.
  by constructor.
Qed.


(*** Type system *)


Inductive ty :=
  | Tnat : ty | Tarr : ty → ty → ty.

Inductive tyctx : scope → Type :=
| empC : tyctx []
| consC : forall{Γ}, ty → tyctx Γ → tyctx (()::Γ)
.

Inductive typed_var : forall {S}, tyctx S → var S → ty → Prop :=
| typed_var_Z S (τ : ty) (Γ : tyctx S) :
  typed_var (consC τ Γ) Vz τ
| typed_var_S S (τ τ' : ty) (Γ : tyctx S) v :
  typed_var Γ v τ →
  typed_var (consC τ' Γ) (Vs v) τ
.

Inductive typed : forall {S}, tyctx S → expr S → ty → Prop :=
| typed_Val {S} (Γ : tyctx S) (τ : ty) (v : val S)  :
  typed_val Γ v τ →
  typed Γ (Val v) τ
| typed_Var {S} (Γ : tyctx S) (τ : ty) (v : var S)  :
  typed_var Γ v τ →
  typed Γ (Var v) τ
| typed_Rec {S} (Γ : tyctx S) (τ1 τ2 : ty) (e : expr (()::()::S) ) :
  typed (consC (Tarr τ1 τ2) (consC τ1 Γ)) e τ2 →
  typed Γ (Rec e) (Tarr τ1 τ2)
| typed_App {S} (Γ : tyctx S) (τ1 τ2 : ty) e1 e2 :
  typed Γ e1 (Tarr τ1 τ2) →
  typed Γ e2 τ1 →
  typed Γ (App e1 e2) τ2
| typed_NatOp {S} (Γ : tyctx S) e1 e2 op :
  typed Γ e1 Tnat →
  typed Γ e2 Tnat →
  typed Γ (NatOp op e1 e2) Tnat
| typed_If {S} (Γ : tyctx S) e0 e1 e2 τ :
  typed Γ e0 Tnat →
  typed Γ e1 τ →
  typed Γ e2 τ →
  typed Γ (If e0 e1 e2) τ
| typed_Input {S} (Γ : tyctx S) :
  typed Γ Input Tnat
with typed_val : forall {S}, tyctx S → val S → ty → Prop :=
| typed_Lit {S} (Γ : tyctx S) n :
  typed_val Γ (Lit n) Tnat
| typed_RecV {S} (Γ : tyctx S) (τ1 τ2 : ty) (e : expr (()::()::S) ) :
  typed (consC (Tarr τ1 τ2) (consC τ1 Γ)) e τ2 →
  typed_val Γ (RecV e) (Tarr τ1 τ2)
.

Equations list_of_tyctx {S} (Γ : tyctx S) : list ty :=
  list_of_tyctx empC := [];
  list_of_tyctx (consC τ Γ') := τ::list_of_tyctx Γ'.
