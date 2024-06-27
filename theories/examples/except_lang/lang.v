From gitrees Require Export prelude effects.io_tape effects.exceptions.
Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

Module Lang (Errors : ExcSig).

  Module _Exc := Exc Errors.

  Import _Exc.

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
  | Throw (err : exc) (e : expr) : expr
  | Catch (err : exc) (e₁ : expr) (e₂ : @expr (inc X)) : expr
  with val {X : Set} :=
  | LitV (n : nat) : val
  | RecV (e : @expr (inc (inc X))) : val
  with cont {X : Set} :=
  | END : cont
  | IfK (e₁ : expr) (e₂ : expr) : cont → cont
  | AppLK (v : val) : cont → cont
  | AppRK (e : expr) : cont → cont
  | NatOpLK (op : nat_op) (v : val) : cont → cont
  | NatOpRK (op : nat_op) (e : expr) : cont → cont
  | ThrowK (err : exc) : cont → cont
  | CatchK (err : exc) (h : @expr (inc X)) : cont → cont.

  Arguments val X%bind : clear implicits.
  Arguments expr X%bind : clear implicits.
  Arguments cont X%bind : clear implicits.
  
  Local Open Scope bind_scope.
  
  Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
    match e with
    | Val v => Val (vmap f v)
    | Var x => Var (f x)
    | App e₁ e₂ => App (emap f e₁) (emap f e₂)
    | NatOp o e₁ e₂ => NatOp o (emap f e₁) (emap f e₂)
    | If e₁ e₂ e₃ => If (emap f e₁) (emap f e₂) (emap f e₃)
    | Throw err e => Throw err (emap f e)
    | Catch err e₁ e₂ => Catch err (emap f e₁) (@emap (inc A) (inc B) (f ↑) e₂)
    end
  with vmap {A B : Set} (f : A [→] B) (v : val A) : val B :=
         match v with
         | LitV n => LitV n
         | RecV e => RecV (emap ((f ↑) ↑) e)
         end
  with kmap {A B : Set} (f : A [→] B) (K : cont A) : cont B :=
         match K with
         | END => END
         | IfK e₁ e₂ K => IfK (emap f e₁) (emap f e₂) (kmap f K)
         | AppLK v K => AppLK (vmap f v) (kmap f K)
         | AppRK e K => AppRK (emap f e) (kmap f K)
         | NatOpLK op v K => NatOpLK op (vmap f v) (kmap f K)
         | NatOpRK op e K => NatOpRK op (emap f e) (kmap f K)
         | ThrowK err K => ThrowK err (kmap f K)
         | CatchK err h K => CatchK err (emap (f ↑) h) (kmap f K)
         end.

#[export] Instance FMap_expr : FunctorCore expr := @emap.
#[export] Instance FMap_val  : FunctorCore val := @vmap.
#[export] Instance FMap_cont : FunctorCore cont := @kmap.

#[export] Instance SPC_expr : SetPureCore expr := @Var.

Fixpoint ebind {A B : Set} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vbind f v)
  | Var x => f x
  | App e₁ e₂ => App (ebind f e₁) (ebind f e₂)
  | NatOp o e₁ e₂ => NatOp o (ebind f e₁) (ebind f e₂)
  | If e₁ e₂ e₃ => If (ebind f e₁) (ebind f e₂) (ebind f e₃)
  | Throw err e => Throw err (ebind f e)
  | Catch err e₁ e₂ => Catch err (ebind f e₁) (ebind (f ↑) e₂)
  end
with vbind {A B : Set} (f : A [⇒] B) (v : val A) : val B :=
       match v with
       | LitV n => LitV n
       | RecV e => RecV (ebind ((f ↑) ↑) e)
       end
.

Fixpoint kbind {A B : Set} (f : A [⇒] B) (K : cont A) : cont B :=
       match K with
       | END => END
       | IfK e₁ e₂ K => IfK (ebind f e₁) (ebind f e₂) (kbind f K) 
       | AppLK v K => AppLK (vbind f v) (kbind f K) 
       | AppRK e K => AppRK (ebind f e) (kbind f K)
       | NatOpLK op v K => NatOpLK op (vbind f v) (kbind f K)
       | NatOpRK op e K => NatOpRK op (ebind f e) (kbind f K)
       | ThrowK err K => ThrowK err (kbind f K)
       | CatchK err h K => CatchK err (ebind (f ↑) h) (kbind f K)
       end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.
#[export] Instance BindCore_val  : BindCore val := @vbind.
#[export] Instance BindCore_cont : BindCore cont := @kbind.

#[export] Instance IP_typ : SetPure expr.
Proof.
  split; intros; reflexivity.
Qed.

Fixpoint vmap_id X (δ : X [→] X) (v : val X) : δ ≡ ı → fmap δ v = v
with emap_id X (δ : X [→] X) (e : expr X) : δ ≡ ı → fmap δ e = e
with kmap_id X (δ : X [→] X) (e : cont X) : δ ≡ ı → fmap δ e = e.
Proof.
  - auto_map_id.
  - auto_map_id.
  - auto_map_id.
Qed.

Fixpoint vmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (v : val A) :
  f ∘ g ≡ h → fmap f (fmap g v) = fmap h v
with emap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : expr A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e
with kmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : cont A) :
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
#[export] Instance Functor_cont : Functor cont.
Proof.
  split; [exact kmap_id | exact kmap_comp].
Qed.

Fixpoint vmap_vbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (v : val A) :
  f ̂ ≡ g → fmap f v = bind g v
with emap_ebind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : expr A) :
  f ̂ ≡ g → fmap f e = bind g e
with kmap_kbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : cont A) :
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
#[export] Instance BindMapPure_cont : BindMapPure cont.
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
       (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (e : cont A) :
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
#[export] Instance BindMapComm_cont : BindMapComm cont.
Proof.
  split; intros; now apply kmap_kbind_comm.
Qed.

Fixpoint vbind_id (A : Set) (f : A [⇒] A) (v : val A) :
  f ≡ ı → bind f v = v
with ebind_id  (A : Set) (f : A [⇒] A) (e : expr A) :
  f ≡ ı → bind f e = e
with kbind_id  (A : Set) (f : A [⇒] A) (e : cont A) :
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
with kbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : cont A) :
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
#[export] Instance Bind_cont : Bind cont.
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

Fixpoint fill {X : Set} (K : cont X) (e : expr X) : expr X :=
  match K with
  | END => e
  | IfK e₁ e₂ K => fill K $ If e e₁ e₂
  | AppLK v K => fill K $ App e (Val v)
  | AppRK e' K => fill K $ App e' e
  | NatOpLK op v K => fill K $ NatOp op e (Val v)
  | NatOpRK op e' K => fill K $ NatOp op e' e
  | ThrowK err K => fill K $ Throw err e
  | CatchK err e' K => fill K $ Catch err e e'
  end.

Lemma fill_emap {X Y : Set} (f : X [→] Y) (K : cont X) (e : expr X)
  : fmap f (fill K e) = fill (fmap f K) (fmap f e).
Proof.
  revert f.
  induction K as [ | ???? IH
                  | ??? IH
                  | ??? IH
                  | ???? IH
                  | ???? IH
                  | ??? IH
                 | ???? IH  ];
    intros f; term_simpl; first done; rewrite IH; reflexivity.
Qed.

Fixpoint cont_compose {S} (K1 K2 : cont S) : cont S
  := match K2 with
     | END => K1
     | IfK e₁ e₂ K => IfK e₁ e₂ (cont_compose K1 K)
     | AppLK v K => AppLK v (cont_compose K1 K)
     | AppRK e K => AppRK e (cont_compose K1 K)
     | NatOpLK op v K => NatOpLK op v (cont_compose K1 K)
     | NatOpRK op e K => NatOpRK op e (cont_compose K1 K)
     | ThrowK err K => ThrowK err (cont_compose K1 K)
     | CatchK err h K => CatchK err h (cont_compose K1 K)
     end.

Fixpoint unwind {S : Set} (err : exc) (k : cont S) :=
  match k with
  | END => None
  | IfK _ _ K' => unwind err K'
  | AppLK _ K' => unwind err K'
  | AppRK _ K' => unwind err K'
  | NatOpLK _ _ K' => unwind err K'
  | NatOpRK _ _ K' => unwind err K'
  | ThrowK _ K' => unwind err K'
  | CatchK err' h K' => if eq_dec err err'
                        then Some (h,K')
                        else unwind err K'
  end.

Variant config {S : Set} : Type :=
  | Cexpr : expr S → config
  | Ccont : cont S → val S → config
  | Ceval : expr S → cont S → config
  | Cret : val S → config.

Reserved Notation "c '===>' c'"
  (at level 40, c' at level 30).

Variant Cred {S : Set} : config → config → Prop :=
  | Cinit e : Cexpr e ===> Ceval e END 
  | Cval v k : Ceval (Val v) k ===> Ccont k v
  | Capp e0 e1 k : Ceval (App e0 e1) k ===> Ceval e1 (AppRK e0 k)
  | Cop op e0 e1 k : Ceval (NatOp op e0 e1) k ===> Ceval e1 (NatOpRK op e0 k)
  | Cif cd e1 e2 k : Ceval (If cd e1 e2) k ===> Ceval cd (IfK e1 e2 k)
  | Ccatch err e h k : Ceval (Catch err e h) k ===> Ceval e (CatchK err h k)
  | Cthrow err e k : Ceval (Throw err e) k ===> Ceval e (ThrowK err k)
  | Cappr e v k : Ccont (AppRK e k) v ===> Ceval e (AppLK v k)
  | Cappl f (v : val S) k : Ccont (AppLK v k) (RecV f) ===> Ceval
                        (subst (Inc := inc)
                           (subst (F := expr) (Inc := inc) f
                              (Val (shift (Inc := inc) v)))
                           (Val (RecV f))) k
  | Cifk n e1 e2 k : Ccont (IfK e1 e2 k) (LitV n) ===> Ceval (if (n =? 0) then e2 else e1) k
  | Coprk op v e k : Ccont (NatOpRK op e k) v ===> Ceval e (NatOpLK op v k)
  | Coplk op v1 v2 v3 k : nat_op_interp op v1 v2 = Some v3 →
                          Ccont (NatOpLK op v2 k) v1 ===> Ceval (Val v3) k
  | Ccatchk err h v k : Ccont (CatchK err h k) v ===> Ceval (Val v) k
  | Cthrowk err h v k k' : unwind err k = Some (h,k') → 
    Ccont (ThrowK err k) v ===> Ceval (subst (Inc := inc) h (Val v)) k'

where "c ===> c'" := (Cred c c').

Inductive steps {S : Set} : (@config S) → (@config S) → Prop :=
| step0 c : steps c c
| step_trans c c' c'' : c ===> c' → steps c' c'' → steps c c''
.

(** Carbonara from heap lang *)
Global Instance fill_item_inj {S} (Ki : cont S) : Inj (=) (=) (fill Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val {S} K (e : expr S) :
  is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [v ?]. induction K; simpl in H; try apply IHK in H.
  1 : eauto.
  all : contradict H; eauto.
Qed.

Lemma fill_app {S} (K1 K2 : cont S) e : fill (cont_compose K1 K2) e = fill K1 (fill K2 e).
Proof.
  revert K1.
  revert e.
  induction K2 as [ | ???? IH
                 | ??? IH
                 | ??? IH
                 | ???? IH
                 | ???? IH
                 | ??? IH
                  | ???? IH  ];
    first done; intros e' K1; simpl;  rewrite IH; reflexivity.
Qed.

Lemma fill_val : ∀ {S} K (e : expr S), is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros S K.
  induction K as [ | ???? IH
                  | ??? IH
                  | ??? IH
                  | ???? IH
                  | ???? IH
                  | ??? IH
                  | ???? IH  ]=> e' //=;
    inversion 1 as [? HH];
    apply IH in H;
    simpl in H;
    contradict H;
    eauto.
Qed.

Lemma fill_not_val : ∀ {S} K (e : expr S), to_val e = None → to_val (fill K e) = None.
Proof.
  intros S K e. rewrite !eq_None_not_Some.
  eauto using fill_val.
Qed.

Lemma fill_end {S} (e : expr S) : fill END e = e.
Proof. reflexivity. Qed.

Lemma fill_comp {S} K1 K2 (e : expr S) : fill K2 (fill K1 e) = fill (cont_compose K2 K1) e.
Proof. by rewrite fill_app. Qed.

Global Instance fill_inj {S} (K : cont S) : Inj (=) (=) (fill K).
Proof.
  induction K as [ | | | | | | | ];
    rewrite /Inj; naive_solver.
Qed.

(*** Type system *)


Inductive ty :=
  | Tnat : ty | Tarr : ty → ty → ty.

Context {ETy : exc → ty}.
          
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
| typed_Throw err exp τ :
  typed Γ exp (ETy err) → typed Γ (Throw err exp) τ
| typed_Catch err exp cexp τ :
  typed Γ exp τ →
  typed (Γ ▹ (ETy err)) cexp τ →
  typed Γ (Catch err exp cexp) τ 
with typed_val {S : Set} (Γ : S -> ty) : val S → ty → Prop :=
| typed_Lit n :
  typed_val Γ (LitV n) Tnat
| typed_RecV (τ1 τ2 : ty) (e : expr (inc (inc S))) :
  typed (Γ ▹ (Tarr τ1 τ2) ▹ τ1) e τ2 →
  typed_val Γ (RecV e) (Tarr τ1 τ2)
.

(** TODO LATER

Declare Scope syn_scope.
Delimit Scope syn_scope with syn.

Coercion Val : val >-> expr.

Coercion App : expr >-> Funclass.
Coercion AppLK : val >-> Funclass.
Coercion AppRK : expr >-> Funclass.


(* XXX: We use these typeclasses to share the notation between the
expressions and the evaluation contexts, for readability. It will be
good to also share the notation between different languages. *)

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

Global Instance OpNotationLK {S : Set} : OpNotation (cont S) (nat_op) (val S) (cont S) := {
  __op K op v := NatOpRK op K v
  }.

Global Instance OpNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : OpNotation (F S) (nat_op) (cont S) (cont S) := {
  __op e op K := NatOpLK op (__asSynExpr e) K
  }.

Class IfNotation (A B C D : Type) := { __if : A -> B -> C -> D }.

Global Instance IfNotationExpr {S : Set} {F G H : Set -> Type} `{AsSynExpr F, AsSynExpr G, AsSynExpr H} : IfNotation (F S) (G S) (H S) (expr S) := {
  __if e₁ e₂ e₃ := If (__asSynExpr e₁) (__asSynExpr e₂) (__asSynExpr e₃)
  }.

Global Instance IfNotationK {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : IfNotation (cont S) (F S) (G S) (cont S) := {
  __if K e₂ e₃ := IfK K (__asSynExpr e₂) (__asSynExpr e₃)
  }.

Class AppNotation (A B C : Type) := { __app : A -> B -> C }.

Global Instance AppNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : AppNotation (F S) (G S) (expr S) := {
  __app e₁ e₂ := App (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance AppNotationLK {S : Set} : AppNotation (cont S) (val S) (cont S) := {
  __app K v := AppLK K v
  }.

Global Instance AppNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : AppNotation (F S) (cont S) (cont S) := {
  __app e K := AppRK (__asSynExpr e) K
  }.

Class ThrowNotation (A B : Type) := { __throw : exc -> A -> B}.

Global Instance ThrowNotationExpr {S : Set} {F: Set -> Type} `{AsSynExpr F} : ThrowNotation (F S) (expr S) :=
  {
    __throw e v := Throw e (__asSynExpr v)
  }.

Global Instance ThrowNotationK {S : Set} : ThrowNotation (cont S) (cont S) :=
  {
    __throw e K := ThrowK e K
  }.

Class CatchNotation (A B C : Type) :=
  {
    __catch : exc -> A -> B -> C
  }.

Global Instance CatchNotationExpr {S : Set} (F G : Set -> Type) `{AsSynExpr F} `{AsSynExpr G} : CatchNotation (F S) (G (inc S)) (expr S) :=
  {
    __catch err b h := Catch err (__asSynExpr b) (__asSynExpr h) 
  }.

Global Instance CatchNotationK {S : Set} (F : Set -> Type) `{AsSynExpr F} : CatchNotation (cont S) (F (inc S)) (cont S) :=
  {
    __catch err K h := CatchK err K (__asSynExpr h)
  }.
 

Notation of_val := Val (only parsing).

Notation "x '⋆' y" := (__app x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '+' y" := (__op x%syn Add y%syn) : syn_scope.
Notation "x '-' y" := (__op x%syn Sub y%syn) : syn_scope.
Notation "x '*' y" := (__op x%syn Mult y%syn) : syn_scope.
Notation "'if' x 'then' y 'else' z" := (__if x%syn y%syn z%syn) : syn_scope.
Notation "'#' n" := (LitV n) (at level 60) : syn_scope.
Notation "'rec' e" := (RecV e%syn) (at level 60) : syn_scope.
Notation "'$' fn" := (set_pure_resolver fn) (at level 60) : syn_scope.
Notation "'try' b 'catch' err '=>' h" :=
  (__catch err b%syn h%syn) (at level 60) : syn_scope.
Notation "'throw' err v" :=
  (__throw err v%syn) (at level 60) : syn_scope.
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
**)
End Lang.
