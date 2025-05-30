From gitrees Require Export prelude effects.exceptions.
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

  Arguments val X%_bind : clear implicits.
  Arguments expr X%_bind : clear implicits.
  Arguments cont X%_bind : clear implicits.

  
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
         end.
  Fixpoint kmap {A B : Set} (f : A [→] B) (K : cont A) : cont B :=
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

Theorem unwind_decompose {S : Set} (err : exc) (K : cont S) (h : expr (inc S)) (K2 : cont S) : unwind err K = Some (h, K2) ↔ ∃ (K1 : cont S), (K = cont_compose (CatchK err h K2) K1
                                                                                                                                               ∧ (∀ K3 K4 h', K1 ≠ cont_compose (CatchK err h' K4) K3 )
                                                                                                                                              ).
Proof.
  induction K.
  - split.
    + intros. done.
    + intros (? & ? & ?).
      destruct x;
      done.
  - split.
    + intros H.
      apply IHK in H.
      destruct H as (K1 & HK1 & HNC).
      exists (IfK e₁ e₂ K1).
      simpl.
      rewrite HK1.
      split; first done.
      intros.
      destruct K3; try done.
      simpl.
      intros [=-> -> ->].
      specialize (HNC K3 K4 h').
      by apply HNC.
      
    + intros (K1 & HK1 & HNC).
      destruct K1; try done.
      simpl.
      apply IHK.
      injection HK1 as <- <- ->.
      eexists.
      split; first done.
      intros K3 K4 h' ->.
      specialize (HNC (IfK e₁ e₂ K3) K4 h').
      by apply HNC.
      
   - split.
    + intros H.
      apply IHK in H.
      destruct H as (K1 & HK1 & HNC).
      exists (AppLK v K1).
      simpl.
      rewrite HK1.
      split; first done.
      intros.
      destruct K3; try done.
      simpl.
      intros [=-> ->].
      specialize (HNC K3 K4 h').
      by apply HNC.
      
    + intros (K1 & HK1 & HNC).
      destruct K1; try done.
      simpl.
      apply IHK.
      injection HK1 as <- ->.
      eexists.
      split; first done.
      intros K3 K4 h' ->.
      specialize (HNC (AppLK v K3) K4 h').
      by apply HNC.
   - split.
    + intros H.
      apply IHK in H.
      destruct H as (K1 & HK1 & HNC).
      exists (AppRK e K1).
      simpl.
      rewrite HK1.
      split; first done.
      intros.
      destruct K3; try done.
      simpl.
      intros [=-> ->].
      specialize (HNC K3 K4 h').
      by apply HNC.
      
    + intros (K1 & HK1 & HNC).
      destruct K1; try done.
      simpl.
      apply IHK.
      injection HK1 as <- ->.
      eexists.
      split; first done.
      intros K3 K4 h' ->.
      specialize (HNC (AppRK e K3) K4 h').
      by apply HNC.
   - split.
    + intros H.
      apply IHK in H.
      destruct H as (K1 & HK1 & HNC).
      exists (NatOpLK op v K1).
      simpl.
      rewrite HK1.
      split; first done.
      intros.
      destruct K3; try done.
      simpl.
      intros [=-> -> ->].
      specialize (HNC K3 K4 h').
      by apply HNC.
      
    + intros (K1 & HK1 & HNC).
      destruct K1; try done.
      simpl.
      apply IHK.
      injection HK1 as <- <- ->.
      eexists.
      split; first done.
      intros K3 K4 h' ->.
      specialize (HNC (NatOpLK op v K3) K4 h').
      by apply HNC.
   - split.
    + intros H.
      apply IHK in H.
      destruct H as (K1 & HK1 & HNC).
      exists (NatOpRK op e K1).
      simpl.
      rewrite HK1.
      split; first done.
      intros.
      destruct K3; try done.
      simpl.
      intros [=-> -> ->].
      specialize (HNC K3 K4 h').
      by apply HNC.
      
    + intros (K1 & HK1 & HNC).
      destruct K1; try done.
      simpl.
      apply IHK.
      injection HK1 as <- <- ->.
      eexists.
      split; first done.
      intros K3 K4 h' ->.
      specialize (HNC (NatOpRK op e K3) K4 h').
      by apply HNC.
   - split.
    + intros H.
      apply IHK in H.
      destruct H as (K1 & HK1 & HNC).
      exists (ThrowK err0 K1).
      simpl.
      rewrite HK1.
      split; first done.
      intros.
      destruct K3; try done.
      simpl.
      intros [=-> ->].
      specialize (HNC K3 K4 h').
      by apply HNC.
      
    + intros (K1 & HK1 & HNC).
      destruct K1; try done.
      simpl.
      apply IHK.
      injection HK1 as <- ->.
      eexists.
      split; first done.
      intros K3 K4 h' ->.
      specialize (HNC (ThrowK err0 K3) K4 h').
      by apply HNC.
 
   - split.
     + intros H.
       simpl in H.
       destruct (eq_dec err err0) as [-> | Hdiff].
       * injection H as -> ->.
         exists END.
         split; first done.
         intros K3 K4 h'.
         destruct K3, K4; done.
       * apply IHK in H.
         destruct H as (K1 & HK1 & HNC).
         exists (CatchK err0 h0 K1).
         simpl.
         rewrite HK1.
         split; first done.
         intros K3 K4 h'.
         destruct K3; try done; simpl; intros [=<- <- ->]; first done.
         by eapply HNC. 
         
     + intros (K1 & HK1 & HNC).
       destruct K1; try done.
       * simpl. 
         destruct (eq_dec err err0) as [-> | C].
         { simpl in HK1. by injection HK1 as -> ->. }
         apply IHK.
         injection HK1 as <- <-.
         by contradict C.
       * injection HK1 as <- <- ->.
         simpl.
         destruct (eq_dec err err0) as [-> | Herr].
         {
           exfalso.
           specialize (HNC END K1 h0).
           by apply HNC.
         }
         apply IHK.
         exists K1.
         split; first done.
         intros K3 K4 h' ->.
         specialize (HNC (CatchK err0 h0 K3)).
         by eapply HNC.
Qed.

Lemma unwind_decompose_weak {S} :
  ∀ (K K1 K2 : cont S) err h, K = cont_compose (CatchK err h K1) K2 →
                              ∃ h' K3, unwind err K = Some (h', K3).
  Proof.
    intros K K1 K2.
    revert K1.
    induction K2; intros K1 err0 h0 ->; try (simpl; by eapply IHK2).
    - simpl. destruct (eq_dec err0 err0); last done.
      by eexists _,_.
    - simpl. destruct (eq_dec err0 err).
      + by eexists _,_.
      + by eapply IHK2.
  Qed.
      
Variant config {S : Set} : Type :=
  | Cexpr : expr S → config
  | Ccont : cont S → val S → config
  | Ceval : expr S → cont S → config
  | Cret : val S → config.

Reserved Notation "c '===>' c' / n"
  (at level 40, c' at level 30).

Variant Cred {S : Set} : config → config → nat → Prop :=
  | Cinit e : Cexpr e ===> Ceval e END / 0
  | Cval v k : Ceval (Val v) k ===> Ccont k v / 0
  | Capp e0 e1 k : Ceval (App e0 e1) k ===> Ceval e1 (AppRK e0 k) / 0
  | Cop op e0 e1 k : Ceval (NatOp op e0 e1) k ===> Ceval e1 (NatOpRK op e0 k) / 0
  | Cif cd e1 e2 k : Ceval (If cd e1 e2) k ===> Ceval cd (IfK e1 e2 k) / 0
  | Ccatch err e h k : Ceval (Catch err e h) k ===> Ceval e (CatchK err h k) / 1
  | Cthrow err e k : Ceval (Throw err e) k ===> Ceval e (ThrowK err k) / 0
  | Cappr e v k : Ccont (AppRK e k) v ===> Ceval e (AppLK v k) / 0
  | Cappl f (v : val S) k : Ccont (AppLK v k) (RecV f) ===> Ceval
                        (subst (Inc := inc)
                           (subst (F := expr) (Inc := inc) f
                              (Val (shift (Inc := inc) v)))
                           (Val (RecV f))) k / 1
  | Cifk n e1 e2 k : Ccont (IfK e1 e2 k) (LitV n) ===> Ceval (if (n =? 0) then e2 else e1) k / 0
  | Coprk op v e k : Ccont (NatOpRK op e k) v ===> Ceval e (NatOpLK op v k) / 0
  | Coplk op v1 v2 v3 k : nat_op_interp op v1 v2 = Some v3 →
                          Ccont (NatOpLK op v2 k) v1 ===> Ceval (Val v3) k / 0
  | Ccatchk err h v k : Ccont (CatchK err h k) v ===> Ceval (Val v) k / 1
  | Cthrowk err h v k k' : unwind err k = Some (h,k') → 
                           Ccont (ThrowK err k) v ===> Ceval (subst (Inc := inc) h (Val v)) k' / 1
  | Cend v : Ccont END v ===> Cret v / 0

where "c ===> c' / n" := (Cred c c' n).

Inductive steps {S : Set} : (@config S) → (@config S) → nat →  Prop :=
| step0 c : steps c c 0
| step_trans c c' c'' n n' : c ===> c' / n → steps c' c'' n' → steps c c'' (n + n')
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

End Lang.
