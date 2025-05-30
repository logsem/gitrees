From gitrees Require Export prelude effects.io_tape.
Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

Inductive nat_op := Add | Sub | Mult.

Inductive expr {X : Set} : Type :=
(* Values *)
| Val (v : val) : expr
| Var (x : X) : expr
(* Base lambda calculus *)
| App (e₁ : expr) (e₂ : expr) : expr
(* Base types and their operations *)
| NatOp (op : nat_op) (e₁ : expr) (e₂ : expr) : expr
| If (e₁ : expr) (e₂ : expr) (e₃ : expr) : expr
(* The effects *)
| Callcc (e : @expr (inc X)) : expr
| Throw (e₁ : expr) (e₂ : expr) : expr
with val {X : Set} :=
| LitV (n : nat) : val
| RecV (e : @expr (inc (inc X))) : val
| ContV (K : ectx) : val
with ectx {X : Set} :=
| EmptyK : ectx
| IfK (K : ectx) (e₁ : expr) (e₂ : expr) : ectx
| AppLK (K : ectx) (v : val) : ectx
| AppRK (e : expr) (K : ectx) : ectx
| NatOpRK (op : nat_op) (e : expr) (K : ectx) : ectx
| NatOpLK (op : nat_op) (K : ectx) (v : val) : ectx
| ThrowLK (K : ectx) (e : expr) : ectx
| ThrowRK (v : val) (K : ectx) : ectx.

Arguments val X%_bind : clear implicits.
Arguments expr X%_bind : clear implicits.
Arguments ectx X%_bind : clear implicits.

Local Open Scope bind_scope.

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vmap f v)
  | Var x => Var (f x)
  | App e₁ e₂ => App (emap f e₁) (emap f e₂)
  | NatOp o e₁ e₂ => NatOp o (emap f e₁) (emap f e₂)
  | If e₁ e₂ e₃ => If (emap f e₁) (emap f e₂) (emap f e₃)
  | Callcc e => Callcc (emap (f ↑) e)
  | Throw e₁ e₂ => Throw (emap f e₁) (emap f e₂)
  end
with vmap {A B : Set} (f : A [→] B) (v : val A) : val B :=
       match v with
       | LitV n => LitV n
       | RecV e => RecV (emap ((f ↑) ↑) e)
       | ContV K => ContV (kmap f K)
       end
with kmap {A B : Set} (f : A [→] B) (K : ectx A) : ectx B :=
       match K with
       | EmptyK => EmptyK
       | IfK K e₁ e₂ => IfK (kmap f K) (emap f e₁) (emap f e₂)
       | AppLK K v => AppLK (kmap f K) (vmap f v)
       | AppRK e K => AppRK (emap f e) (kmap f K)
       | NatOpRK op e K => NatOpRK op (emap f e) (kmap f K)
       | NatOpLK op K v => NatOpLK op (kmap f K) (vmap f v)
       | ThrowLK K e => ThrowLK (kmap f K) (emap f e)
       | ThrowRK v K => ThrowRK (vmap f v) (kmap f K)
       end.
#[export] Instance FMap_expr : FunctorCore expr := @emap.
#[export] Instance FMap_val  : FunctorCore val := @vmap.
#[export] Instance FMap_ectx  : FunctorCore ectx := @kmap.

#[export] Instance SPC_expr : SetPureCore expr := @Var.

Fixpoint ebind {A B : Set} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vbind f v)
  | Var x => f x
  | App e₁ e₂ => App (ebind f e₁) (ebind f e₂)
  | NatOp o e₁ e₂ => NatOp o (ebind f e₁) (ebind f e₂)
  | If e₁ e₂ e₃ => If (ebind f e₁) (ebind f e₂) (ebind f e₃)
  | Callcc e => Callcc (ebind (f ↑) e)
  | Throw e₁ e₂ => Throw (ebind f e₁) (ebind f e₂)
  end
with vbind {A B : Set} (f : A [⇒] B) (v : val A) : val B :=
       match v with
       | LitV n => LitV n
       | RecV e => RecV (ebind ((f ↑) ↑) e)
       | ContV K => ContV (kbind f K)
       end
with kbind {A B : Set} (f : A [⇒] B) (K : ectx A) : ectx B :=
       match K with
       | EmptyK => EmptyK
       | IfK K e₁ e₂ => IfK (kbind f K) (ebind f e₁) (ebind f e₂)
       | AppLK K v => AppLK (kbind f K) (vbind f v)
       | AppRK e K => AppRK (ebind f e) (kbind f K)
       | NatOpRK op e K => NatOpRK op (ebind f e) (kbind f K)
       | NatOpLK op K v => NatOpLK op (kbind f K) (vbind f v)
       | ThrowLK K e => ThrowLK (kbind f K) (ebind f e)
       | ThrowRK v K => ThrowRK (vbind f v) (kbind f K)
       end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.
#[export] Instance BindCore_val  : BindCore val := @vbind.
#[export] Instance BindCore_ectx  : BindCore ectx := @kbind.

#[export] Instance IP_typ : SetPure expr.
Proof.
  split; intros; reflexivity.
Qed.

Fixpoint vmap_id X (δ : X [→] X) (v : val X) : δ ≡ ı → fmap δ v = v
with emap_id X (δ : X [→] X) (e : expr X) : δ ≡ ı → fmap δ e = e
with kmap_id X (δ : X [→] X) (e : ectx X) : δ ≡ ı → fmap δ e = e.
Proof.
  - auto_map_id.
  - auto_map_id.
  - auto_map_id.
Qed.

Fixpoint vmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (v : val A) :
  f ∘ g ≡ h → fmap f (fmap g v) = fmap h v
with emap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : expr A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e
with kmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : ectx A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e.
Proof.
  - auto_map_comp.
  - auto_map_comp.
  - auto_map_comp.
Qed.

#[export] Instance Functor_val : Functor val.
Proof.
  split; [exact vmap_id | exact vmap_comp].
Qed.
#[export] Instance Functor_expr : Functor expr.
Proof.
  split; [exact emap_id | exact emap_comp].
Qed.
#[export] Instance Functor_ectx : Functor ectx.
Proof.
  split; [exact kmap_id | exact kmap_comp].
Qed.

Fixpoint vmap_vbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (v : val A) :
  f ̂ ≡ g → fmap f v = bind g v
with emap_ebind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : expr A) :
  f ̂ ≡ g → fmap f e = bind g e
with kmap_kbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : ectx A) :
  f ̂ ≡ g → fmap f e = bind g e.
Proof.
  - auto_map_bind_pure.
    erewrite emap_ebind_pure; [reflexivity |].
    intros [| [| x]]; term_simpl; [reflexivity | reflexivity |].
    rewrite <-(EQ x).
    reflexivity.
  - auto_map_bind_pure.
  - auto_map_bind_pure.
Qed.

#[export] Instance BindMapPure_val : BindMapPure val.
Proof.
  split; intros; now apply vmap_vbind_pure.
Qed.
#[export] Instance BindMapPure_expr : BindMapPure expr.
Proof.
  split; intros; now apply emap_ebind_pure.
Qed.
#[export] Instance BindMapPure_ectx : BindMapPure ectx.
Proof.
  split; intros; now apply kmap_kbind_pure.
Qed.

Fixpoint vmap_vbind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
  (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (v : val A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ v) = fmap f₁ (bind g₁ v)
with emap_ebind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
       (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (e : expr A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e)
with kmap_kbind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
       (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (e : ectx A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e).
Proof.
  - auto_map_bind_comm.
    erewrite emap_ebind_comm; [reflexivity |].
    erewrite lift_comm; [reflexivity |].
    erewrite lift_comm; [reflexivity | assumption].
  - auto_map_bind_comm.
  - auto_map_bind_comm.
Qed.

#[export] Instance BindMapComm_val : BindMapComm val.
Proof.
  split; intros; now apply vmap_vbind_comm.
Qed.
#[export] Instance BindMapComm_expr : BindMapComm expr.
Proof.
  split; intros; now apply emap_ebind_comm.
Qed.
#[export] Instance BindMapComm_ectx : BindMapComm ectx.
Proof.
  split; intros; now apply kmap_kbind_comm.
Qed.

Fixpoint vbind_id (A : Set) (f : A [⇒] A) (v : val A) :
  f ≡ ı → bind f v = v
with ebind_id  (A : Set) (f : A [⇒] A) (e : expr A) :
  f ≡ ı → bind f e = e
with kbind_id  (A : Set) (f : A [⇒] A) (e : ectx A) :
  f ≡ ı → bind f e = e.
Proof.
  - auto_bind_id.
    rewrite ebind_id; [reflexivity |].
    apply lift_id, lift_id; assumption.
  - auto_bind_id.
  - auto_bind_id.
Qed.

Fixpoint vbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (v : val A) :
  f ∘ g ≡ h → bind f (bind g v) = bind h v
with ebind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : expr A) :
  f ∘ g ≡ h → bind f (bind g e) = bind h e
with kbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : ectx A) :
  f ∘ g ≡ h → bind f (bind g e) = bind h e.
Proof.
  - auto_bind_comp.
    erewrite ebind_comp; [reflexivity |].
    erewrite lift_comp; [reflexivity |].
    erewrite lift_comp; [reflexivity | assumption].
  - auto_bind_comp.
  - auto_bind_comp.
Qed.

#[export] Instance Bind_val : Bind val.
Proof.
  split; intros; [now apply vbind_id | now apply vbind_comp].
Qed.
#[export] Instance Bind_expr : Bind expr.
Proof.
  split; intros; [now apply ebind_id | now apply ebind_comp].
Qed.
#[export] Instance Bind_ectx : Bind ectx.
Proof.
  split; intros; [now apply kbind_id | now apply kbind_comp].
Qed.

Definition to_val {S} (e : expr S) : option (val S) :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition do_natop (op : nat_op) (x y : nat) : nat :=
  match op with
  | Add => plus x y
  | Sub => minus x y
  | Mult => mult x y
  end.

Definition nat_op_interp {S} (n : nat_op) (x y : val S) : option (val S) :=
  match x, y with
  | LitV x, LitV y => Some $ LitV $ do_natop n x y
  | _,_ => None
  end.

Fixpoint fill {X : Set} (K : ectx X) (e : expr X) : expr X :=
  match K with
  | EmptyK => e
  | IfK K e₁ e₂ => If (fill K e) e₁ e₂
  | AppLK K v => App (fill K e) (Val v)
  | AppRK e' K => App e' (fill K e)
  | NatOpRK op e' K => NatOp op e' (fill K e)
  | NatOpLK op K v => NatOp op (fill K e) (Val v)
  | ThrowLK K e' => Throw (fill K e) e'
  | ThrowRK v K => Throw (Val v) (fill K e)
  end.

Lemma fill_emap {X Y : Set} (f : X [→] Y) (K : ectx X) (e : expr X)
  : fmap f (fill K e) = fill (fmap f K) (fmap f e).
Proof.
  revert f.
  induction K as [| ?? IH
                 | ?? IH
                 | ??? IH
                 | ???? IH
                 | ??? IH
                 | ?? IH
                 | ??? IH];
    intros f; term_simpl; first done; rewrite IH; reflexivity.
Qed.

(*** Operational semantics *)

Inductive head_step {S} : expr S → expr S → ectx S → nat * nat → Prop :=
| BetaS e1 v2 K :
  head_step (App (Val $ RecV e1) (Val v2)) (subst (Inc := inc) ((subst (F := expr) (Inc := inc) e1) (Val (shift (Inc := inc) v2))) (Val (RecV e1))) K (1,0)
| NatOpS op v1 v2 v3 K :
  nat_op_interp op v1 v2 = Some v3 →
  head_step (NatOp op (Val v1) (Val v2))
            (Val v3) K (0, 0)
| IfTrueS n e1 e2 K :
  n > 0 →
  head_step (If (Val (LitV n)) e1 e2)
            e1 K (0, 0)
| IfFalseS n e1 e2 K :
  n = 0 →
  head_step (If (Val (LitV n)) e1 e2)
    e2 K (0, 0)
| CallccS e K :
  head_step (Callcc e) (subst (Inc := inc) e (Val (ContV K))) K (1, 1)
.

Lemma head_step_01 {S} (e1 e2 : expr S) K n m :
  head_step e1 e2 K (n,m) → m = 0 ∨ m = 1.
Proof.  inversion 1; eauto. Qed.
Lemma head_step_unfold_01 {S} (e1 e2 : expr S) K n m :
  head_step e1 e2 K (n,m) → n = 0 ∨ n = 1.
Proof.  inversion 1; eauto. Qed.
(* Lemma head_step_no_io {S} (e1 e2 : expr S) K n : *)
(*   head_step e1 e2 K (n,0) → σ1 = σ2. *)
(* Proof.  inversion 1; eauto. Qed. *)

(** Carbonara from heap lang *)
Global Instance fill_item_inj {S} (Ki : ectx S) : Inj (=) (=) (fill Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val {S} Ki (e : expr S) :
  is_Some (to_val (fill Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck {S} (e1 : expr S) e2 K m : head_step e1 e2 K m → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Fixpoint ectx_compose {S} (K1 K2 : ectx S) : ectx S
  := match K1 with
     | EmptyK => K2
     | IfK K e₁ e₂ => IfK (ectx_compose K K2) e₁ e₂
     | AppLK K v => AppLK (ectx_compose K K2) v
     | AppRK e K => AppRK e (ectx_compose K K2)
     | NatOpRK op e K => NatOpRK op e (ectx_compose K K2)
     | NatOpLK op K v => NatOpLK op (ectx_compose K K2) v
     | ThrowLK K e => ThrowLK (ectx_compose K K2) e
     | ThrowRK v K => ThrowRK v (ectx_compose K K2)
     end.

Lemma fill_app {S} (K1 K2 : ectx S) e : fill (ectx_compose K1 K2) e = fill K1 (fill K2 e).
Proof.
  revert K2.
  revert e.
  induction K1 as [| ?? IH
                  | ?? IH
                  | ??? IH
                  | ???? IH
                  | ??? IH
                  | ?? IH
                  | ??? IH];
    simpl; first done; intros e' K2; rewrite IH; reflexivity.
Qed.

Lemma fill_val : ∀ {S} K (e : expr S), is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros S K.
  induction K as [| ?? IH
                 | ?? IH
                 | ??? IH
                 | ???? IH
                 | ??? IH
                 | ?? IH
                 | ??? IH]=> e' //=;
                              inversion 1 as [? HH]; inversion HH.
Qed.

Lemma fill_not_val : ∀ {S} K (e : expr S), to_val e = None → to_val (fill K e) = None.
Proof.
  intros S K e. rewrite !eq_None_not_Some.
  eauto using fill_val.
Qed.

Lemma fill_empty {S} (e : expr S) : fill EmptyK e = e.
Proof. reflexivity. Qed.
Lemma fill_comp {S} K1 K2 (e : expr S) : fill K2 (fill K1 e) = fill (ectx_compose K2 K1) e.
Proof. by rewrite fill_app. Qed.
Global Instance fill_inj {S} (K : ectx S) : Inj (=) (=) (fill K).
Proof.
  induction K as [| ?? IH
                 | ?? IH
                 | ??? IH
                 | ???? IH
                 | ??? IH
                 | ?? IH
                 | ??? IH];
    rewrite /Inj; naive_solver.
Qed.

Inductive prim_step {S} : ∀ (e1 : expr S)
          (e2 : expr S) (n : nat * nat), Prop :=
| Ectx_step e1 e2 n (K : ectx S) e1' e2' :
  e1 = fill K e1' → e2 = fill K e2' →
  head_step e1' e2' K n → prim_step e1 e2 n
| Throw_step e1 e2 (K : ectx S) v K' :
  e1 = (fill K (Throw (Val v) (Val (ContV K')))) ->
  e2 = (fill K' (Val v)) ->
  prim_step e1 e2 (2, 0).

Inductive prim_steps {S} : expr S → expr S → nat * nat → Prop :=
| prim_steps_zero e :
  prim_steps e e (0, 0)
| prim_steps_abit e1 e2 e3 n1 m1 n2 m2 :
  prim_step e1 e2 (n1, m1) →
  prim_steps e2 e3 (n2, m2) →
  prim_steps e1 e3 (plus n1 n2, plus m1 m2)
.

Lemma Ectx_step' {S} (K : ectx S) e1 e2 efs :
  head_step e1 e2 K efs → prim_step (fill K e1) (fill K e2) efs.
Proof. econstructor; eauto. Qed.

Lemma prim_steps_app {S} nm1 nm2 (e1 e2 e3 : expr S) :
  prim_steps e1 e2 nm1 → prim_steps e2 e3 nm2 →
  prim_steps e1 e3 (plus nm1.1 nm2.1, plus nm1.2 nm2.2).
Proof.
  intros Hst. revert nm2.
  induction Hst; intros [n' m']; simplify_eq/=; first done.
  rewrite -!Nat.add_assoc. intros Hsts.
  econstructor; eauto.
  by apply (IHHst (n',m')).
Qed.

Lemma prim_step_steps {S} nm (e1 e2 : expr S) :
  prim_step e1 e2 nm → prim_steps e1 e2 nm.
Proof.
  destruct nm as [n m]. intro Hs.
  rewrite -(Nat.add_0_r n).
  rewrite -(Nat.add_0_r m).
  econstructor; eauto.
  by constructor.
Qed.

Lemma prim_step_steps_steps {S} (e1 e2 e3 : expr S) nm1 nm2 nm3 :
  nm3 = (plus nm1.1 nm2.1, plus nm1.2 nm2.2) ->
  prim_step e1 e2 nm1 → prim_steps e2 e3 nm2 -> prim_steps e1 e3 nm3.
Proof.
  intros -> H G.
  eapply prim_steps_app; last apply G.
  apply prim_step_steps, H.
Qed.

Lemma head_step_prim_step {S} (e1 e2 : expr S) nm :
  head_step e1 e2 EmptyK nm -> prim_step e1 e2 nm.
Proof.
  assert (e1 = fill EmptyK e1) as Heq1; first done.
  rewrite ->Heq1 at 2.
  assert (e2 = fill EmptyK e2) as Heq2; first done.
  rewrite ->Heq2 at 2.
  apply Ectx_step'.
Qed.

(*** Type system *)

Inductive ty :=
  | Tnat : ty | Tarr : ty → ty → ty | Tcont : ty → ty.

Inductive typed {S : Set} (Γ : S -> ty) : expr S → ty → Prop :=
| typed_Val (τ : ty) (v : val S)  :
  typed_val Γ v τ →
  typed Γ (Val v) τ
| typed_Var (τ : ty) (v : S)  :
  Γ v = τ →
  typed Γ (Var v) τ
| typed_App (τ1 τ2 : ty) e1 e2 :
  typed Γ e1 (Tarr τ1 τ2) →
  typed Γ e2 τ1 →
  typed Γ (App e1 e2) τ2
| typed_NatOp e1 e2 op :
  typed Γ e1 Tnat →
  typed Γ e2 Tnat →
  typed Γ (NatOp op e1 e2) Tnat
| typed_If e0 e1 e2 τ :
  typed Γ e0 Tnat →
  typed Γ e1 τ →
  typed Γ e2 τ →
  typed Γ (If e0 e1 e2) τ
| typed_Throw e1 e2 τ τ' :
  typed Γ e1 τ ->
  typed Γ e2 (Tcont τ) ->
  typed Γ (Throw e1 e2) τ'
| typed_Callcc e τ :
  typed (Γ ▹ Tcont τ) e τ ->
  typed Γ (Callcc e) τ
with typed_val {S : Set} (Γ : S -> ty) : val S → ty → Prop :=
| typed_Lit n :
  typed_val Γ (LitV n) Tnat
| typed_RecV (τ1 τ2 : ty) (e : expr (inc (inc S))) :
  typed (Γ ▹ (Tarr τ1 τ2) ▹ τ1) e τ2 →
  typed_val Γ (RecV e) (Tarr τ1 τ2)
.

Declare Scope syn_scope.
Delimit Scope syn_scope with syn.

Coercion Val : val >-> expr.

Coercion App : expr >-> Funclass.
Coercion AppLK : ectx >-> Funclass.
Coercion AppRK : expr >-> Funclass.

Class AsSynExpr (F : Set -> Type) := { __asSynExpr : ∀ S, F S -> expr S }.

Arguments __asSynExpr {_} {_} {_}.

Global Instance AsSynExprValue : AsSynExpr val := {
    __asSynExpr _ v := Val v
  }.
Global Instance AsSynExprExpr : AsSynExpr expr := {
    __asSynExpr _ e := e
  }.

Class OpNotation (A B C D : Type) := { __op : A -> B -> C -> D }.

Global Instance OpNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : OpNotation (F S) nat_op (G S) (expr S) := {
  __op e₁ op e₂ := NatOp op (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance OpNotationLK {S : Set} : OpNotation (ectx S) (nat_op) (val S) (ectx S) := {
  __op K op v := NatOpLK op K v
  }.

Global Instance OpNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : OpNotation (F S) (nat_op) (ectx S) (ectx S) := {
  __op e op K := NatOpRK op (__asSynExpr e) K
  }.

Class IfNotation (A B C D : Type) := { __if : A -> B -> C -> D }.

Global Instance IfNotationExpr {S : Set} {F G H : Set -> Type} `{AsSynExpr F, AsSynExpr G, AsSynExpr H} : IfNotation (F S) (G S) (H S) (expr S) := {
  __if e₁ e₂ e₃ := If (__asSynExpr e₁) (__asSynExpr e₂) (__asSynExpr e₃)
  }.

Global Instance IfNotationK {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : IfNotation (ectx S) (F S) (G S) (ectx S) := {
  __if K e₂ e₃ := IfK K (__asSynExpr e₂) (__asSynExpr e₃)
  }.

Class ThrowNotation (A B C : Type) := { __throw : A -> B -> C }.

Global Instance ThrowNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : ThrowNotation (F S) (G S) (expr S) := {
  __throw e₁ e₂ := Throw (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance ThrowNotationLK {S : Set} {F : Set -> Type} `{AsSynExpr F} : ThrowNotation (ectx S) (F S) (ectx S) := {
  __throw K e₂ := ThrowLK K (__asSynExpr e₂)
  }.

Global Instance ThrowNotationRK {S : Set} : ThrowNotation (val S) (ectx S) (ectx S) := {
  __throw v K := ThrowRK v K
  }.

Class AppNotation (A B C : Type) := { __app : A -> B -> C }.

Global Instance AppNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : AppNotation (F S) (G S) (expr S) := {
  __app e₁ e₂ := App (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance AppNotationLK {S : Set} : AppNotation (ectx S) (val S) (ectx S) := {
  __app K v := AppLK K v
  }.

Global Instance AppNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : AppNotation (F S) (ectx S) (ectx S) := {
  __app e K := AppRK (__asSynExpr e) K
  }.

Notation of_val := Val (only parsing).

Notation "x '⋆' y" := (__app x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '+' y" := (__op x%syn Add y%syn) : syn_scope.
Notation "x '-' y" := (__op x%syn Sub y%syn) : syn_scope.
Notation "x '*' y" := (__op x%syn Mult y%syn) : syn_scope.
Notation "'if' x 'then' y 'else' z" := (__if x%syn y%syn z%syn) : syn_scope.
Notation "'throw' e₁ e₂" := (__throw e₁%syn e₂%syn) (at level 60) : syn_scope.
Notation "'#' n" := (LitV n) (at level 60) : syn_scope.
Notation "'rec' e" := (RecV e%syn) (at level 60) : syn_scope.
Notation "'callcc' e" := (Callcc e%syn) (at level 60) : syn_scope.
Notation "'cont' K" := (ContV K%syn) (at level 60) : syn_scope.
Notation "'$' fn" := (set_pure_resolver fn) (at level 60) : syn_scope.
Notation "□" := (EmptyK) : syn_scope.
Notation "K '⟪' e '⟫'" := (fill K%syn e%syn) (at level 60) : syn_scope.

Definition LamV {S : Set} (e : expr (inc S)) : val S :=
  RecV (shift e).

Notation "'λ' . e" := (LamV e%syn) (at level 60) : syn_scope.

Definition LetE {S : Set} (e : expr S) (e' : expr (inc S)) : expr S :=
  App (LamV e') (e).

Notation "'let_' e₁ 'in' e₂" := (LetE e₁%syn e₂%syn) (at level 60, right associativity) : syn_scope.

Definition SeqE {S : Set} (e e' : expr S) : expr S :=
  App (LamV (shift e)) e'.

Notation "e₁ ';;' e₂" := (SeqE e₁%syn e₂%syn) : syn_scope.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Notation "'ℕ'" := (Tnat) (at level 1) : typ_scope.
Notation "A →ₜ B" := (Tarr A%typ B%typ)
                       (right associativity, at level 60) : typ_scope.
Notation "A 'cont'" := (Tcont A%typ)
                         (at level 60) : typ_scope.

Declare Scope typing_scope.
Delimit Scope typing_scope with typing.

Class TypingNotation (A B C : Type) := { __typing : A -> B -> C -> Prop }.

Notation "Γ ⊢ e : τ" := (__typing Γ e%syn τ%typ) (at level 70, e at level 60) : typing_scope.

Global Instance TypingNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} : TypingNotation (S -> ty) (F S) ty := {
    __typing Γ e τ := typed Γ (__asSynExpr e) τ
  }.

Global Instance TypingNotationVal {S : Set} : TypingNotation (S -> ty) (val S) ty := {
    __typing Γ e τ := typed_val Γ e τ
  }.

Module SynExamples.

  Open Scope syn_scope.

  Example test1 : expr (inc ∅) := ($ 0).
  Example test2 : val ∅ := (rec (if ($ 1) then # 1 else # 0)).
  Example test3 : expr ∅ := (callcc ($ 0)).
  Example test4 : expr ∅ := ((# 1) + (# 0)).
  Example test5 : val ∅ := (rec (if ($ 1) then # 1 else (($ 0) ⋆ (($ 1) - (# 1))))).
  Example test6 : expr (inc (inc ∅)) := ($ 0) ⋆ ($ 1).

  Open Scope typing_scope.

  Example test8 : Prop := (empty_env ⊢ (# 0) : ℕ).
End SynExamples.
