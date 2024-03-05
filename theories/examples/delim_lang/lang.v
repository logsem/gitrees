From gitrees Require Export prelude.

Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.
(* Require Import FunctionalExtensionality. *)

Variant nat_op := Add | Sub | Mult.

Inductive expr {X : Set} :=
(* Values *)
| Val (v : val) : expr
| Var (x : X) : expr
(* Base lambda calculus *)
| App (e₁ : expr) (e₂ : expr) : expr
(* special application for continuations *)
| AppCont (e₁ : expr) (e₂ : expr) : expr
(* Base types and their operations *)
| NatOp (op : nat_op) (e₁ : expr) (e₂ : expr) : expr
| If (e₁ : expr) (e₂ : expr) (e₃ : expr) : expr
(* The effects *)
| Shift (e : @expr (inc X)) : expr
| Reset (e : expr) : expr
with val {X : Set} :=
| LitV (n : nat) : val
| RecV (e : @expr (inc (inc X))) : val
| ContV (k : cont) : val
with cont {X : Set} :=
| END : cont
| IfK (e1 : expr) (e2 : expr) : cont -> cont
| AppLK (v : val) : cont -> cont (* ◻ v *)
| AppRK (e : expr) : cont -> cont (* e ◻ *)
| AppContLK (v : val) : cont -> cont (* ◻ v *)
| AppContRK (e : expr) : cont -> cont (* e ◻ *)
| NatOpLK (op : nat_op) (v : val) : cont -> cont (* ◻ + v *)
| NatOpRK (op : nat_op) (e : expr) : cont -> cont. (* e + ◻ *)

(* conts are inside-out contexts: eg
 IfK e1 e2 (AppLK v ◻) ==> App (if ◻ then e1 else e2) v*)


Arguments val X%bind : clear implicits.
Arguments expr X%bind : clear implicits.
Arguments cont X%bind : clear implicits.

Local Open Scope bind_scope.

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vmap f v)
  | Var x => Var (f x)
  | App e₁ e₂ => App (emap f e₁) (emap f e₂)
  | AppCont e₁ e₂ => AppCont (emap f e₁) (emap f e₂)
  | NatOp o e₁ e₂ => NatOp o (emap f e₁) (emap f e₂)
  | If e₁ e₂ e₃ => If (emap f e₁) (emap f e₂) (emap f e₃)
  | Shift e => Shift (emap (f ↑) e)
  | Reset e => Reset (emap f e)
  end
with
vmap {A B : Set} (f : A [→] B) (v : val A) : val B :=
  match v with
  | LitV n => LitV n
  | RecV e => RecV (emap ((f ↑) ↑) e)
  | ContV k => ContV (kmap f k)
  end
with kmap {A B : Set} (f : A [→] B) (K : cont A) : cont B :=
   match K with
   | END => END
   | IfK e1 e2 k => IfK (emap f e1) (emap f e2) (kmap f k)
   | AppLK v k => AppLK (vmap f v) (kmap f k)
   | AppRK e k => AppRK (emap f e) (kmap f k)
   | AppContLK v k => AppContLK (vmap f v) (kmap f k)
   | AppContRK e k => AppContRK (emap f e) (kmap f k)
   | NatOpLK op v k => NatOpLK op (vmap f v) (kmap f k)
   | NatOpRK op e k => NatOpRK op (emap f e) (kmap f k)
   end.


#[export] Instance FMap_expr : FunctorCore expr := @emap.
#[export] Instance FMap_val  : FunctorCore val := @vmap.
#[export] Instance FMap_cont  : FunctorCore cont := @kmap.

#[export] Instance SPC_expr : SetPureCore expr := @Var.

Fixpoint ebind {A B : Set} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vbind f v)
  | Var x => f x
  | App e₁ e₂ => App (ebind f e₁) (ebind f e₂)
  | AppCont e₁ e₂ => AppCont (ebind f e₁) (ebind f e₂)
  | NatOp o e₁ e₂ => NatOp o (ebind f e₁) (ebind f e₂)
  | If e₁ e₂ e₃ => If (ebind f e₁) (ebind f e₂) (ebind f e₃)
  | Shift e => Shift (ebind (f ↑) e)
  | Reset e => Reset (ebind f e)
  end
with
vbind {A B : Set} (f : A [⇒] B) (v : val A) : val B :=
  match v with
  | LitV n => LitV n
  | RecV e => RecV (ebind ((f ↑) ↑) e)
  | ContV k => ContV (kbind f k)
  end
with kbind {A B : Set} (f : A [⇒] B) (K : cont A) : cont B :=
   match K with
   | END => END
   | IfK e1 e2 k => IfK (ebind f e1) (ebind f e2) (kbind f k)
   | AppLK v k => AppLK (vbind f v) (kbind f k)
   | AppRK e k => AppRK (ebind f e) (kbind f k)
   | AppContLK v k => AppContLK (vbind f v) (kbind f k)
   | AppContRK e k => AppContRK (ebind f e) (kbind f k)
   | NatOpLK op v k => NatOpLK op (vbind f v) (kbind f k)
   | NatOpRK op e k => NatOpRK op (ebind f e) (kbind f k)
   end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.
#[export] Instance BindCore_val  : BindCore val := @vbind.
#[export] Instance BindCore_cont  : BindCore cont := @kbind.

#[export] Instance IP_typ : SetPure expr.
Proof.
  split; intros; reflexivity.
Qed.

Fixpoint vmap_id X (δ : X [→] X) (v : val X) : δ ≡ ı → fmap δ v = v
with emap_id X (δ : X [→] X) (e : expr X) : δ ≡ ı → fmap δ e = e
with kmap_id X (δ : X [→] X) (k : cont X) : δ ≡ ı → fmap δ k = k.
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
  | IfK e1 e2 K => fill K (If e e1 e2)
  | END => e
  | AppLK v K => fill K (App e (Val v))
  | AppRK el K => fill K (App el e)
  | AppContLK v K => fill K (AppCont e (Val v))
  | AppContRK el K => fill K (AppCont el e)
  | NatOpLK op v K => fill K (NatOp op e (Val v))
  | NatOpRK op el K => fill K (NatOp op el e)
  end.


(*** Continuation operations *)


Global Instance fill_inj {S} (Ki : cont S) : Inj (=) (=) (fill Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_val {S} Ki (e : expr S) :
  is_Some (to_val (fill Ki e)) → is_Some (to_val e).
Proof.
  elim: Ki e; simpl in *; intros; first done;
    apply H in H0; simpl in H0; contradiction (is_Some_None H0).
Qed.

(* K1 ∘ K2 *)
Fixpoint cont_compose {S} (K1 K2 : cont S) : cont S :=
  match K2 with
  | END => K1
  | IfK e1 e2 K => IfK e1 e2 (cont_compose K1 K)
  | AppLK v K => AppLK v (cont_compose K1 K)
  | AppRK e K => AppRK e (cont_compose K1 K)
  | AppContLK v K => AppContLK v (cont_compose K1 K)
  | AppContRK e K => AppContRK e (cont_compose K1 K)
  | NatOpLK op v K => NatOpLK op v (cont_compose K1 K)
  | NatOpRK op e K => NatOpRK op e (cont_compose K1 K)
  end.

Lemma fill_comp {S} (K1 K2 : cont S) e : fill (cont_compose K1 K2) e = fill K1 (fill K2 e).
Proof.
  elim: K2 K1 e =>>; eauto;
  intros H K1 e; simpl; by rewrite H.
Qed.


Lemma fill_not_val : ∀ {S} K (e : expr S), to_val e = None → to_val (fill K e) = None.
Proof.
  intros S K e. rewrite !eq_None_not_Some.
  eauto using fill_val.
Qed.


(*** Abstract Machine semantics *)

Definition Mcont {S} := list $ cont S.

Variant config {S} : Type :=
  | Ceval : expr S -> cont S -> @Mcont S -> config
  | Ccont : cont S -> val S -> @Mcont S -> config
  | Cmcont : @Mcont S -> val S -> config
  | Cexpr : expr S -> config
  | Cret : val S -> config.

Reserved Notation "c '===>' c' / nm"
  (at level 40, c', nm at level 30).

Variant Cred {S : Set} : config -> config -> (nat * nat) -> Prop :=

  (* init *)
  | Ceval_init : forall (e : expr S),
      Cexpr e ===> Ceval e END [] / (0,0)

  (* eval *)
  | Ceval_val : forall v k mk,
      Ceval (Val v) k mk ===> Ccont k v mk / (0,0)

  | Ceval_app : forall e0 e1 k mk,
      Ceval (App e0 e1) k mk ===> Ceval e1 (AppRK e0 k) mk / (0,0)

  | Ceval_app_cont : forall e0 e1 k mk,
      Ceval (AppCont e0 e1) k mk ===> Ceval e1 (AppContRK e0 k) mk / (0,0)

  | Ceval_natop : forall op e0 e1 k mk,
      Ceval (NatOp op e0 e1) k mk ===> Ceval e1 (NatOpRK op e0 k) mk / (0,0)

  | Ceval_if : forall eb et ef k mk,
      Ceval (If eb et ef) k mk ===> Ceval eb (IfK et ef k) mk / (0,0)

  | Ceval_reset : forall e k mk,
      Ceval (Reset e) k mk ===> Ceval e END (k :: mk) / (1, 1)

  | Ceval_shift : forall (e : expr $ inc S) k mk,
      Ceval (Shift e) k mk ===>
        Ceval (subst (Inc := inc) e (Val $ ContV k))
        END mk / (1, 1)

  (* cont *)
  | Ccont_end : forall v mk,
      Ccont END v mk ===> Cmcont mk v / (0,0)

  | Ccont_appr : forall e v k mk,
      Ccont (AppRK e k) v mk ===> Ceval e (AppLK v k) mk / (0, 0)

  | Ccont_app_contr : forall e v k mk,
      Ccont (AppContRK e k) v mk ===> Ceval e (AppContLK v k) mk / (0, 0)

  | Ccont_appl : forall e v k mk,
      Ccont (AppLK v k) (RecV e) mk ===>
        Ceval (subst (Inc := inc)
                 (subst (F := expr) (Inc := inc) e
                    (Val (shift (Inc := inc) v)))
                 (Val (RecV e))) k mk / (1, 0)

  | Ccont_cont : forall v k k' mk,
      Ccont (AppContLK v k) (ContV k') mk ===>
        Ccont k' v (k :: mk) / (2, 1)

  | Ccont_if : forall et ef n k mk,
      Ccont (IfK et ef k) (LitV n) mk ===>
        Ceval (if (n =? 0) then ef else et) k mk / (0, 0)

  | Ccont_natopr : forall op e v k mk,
      Ccont (NatOpRK op e k) v mk ===>
        Ceval e (NatOpLK op v k) mk / (0, 0)

  | Ccont_natopl : forall op v0 v1 v2 k mk,
      nat_op_interp op v0 v1 = Some v2 ->
      Ccont (NatOpLK op v1 k) v0 mk ===>
        Ceval (Val v2) k mk / (0,0)

  (* meta-cont *)
  | Cmcont_cont : forall k mk v,
      Cmcont (k :: mk) v ===> Ccont k v mk / (1,1)

  | Cmcont_ret : forall v,
      Cmcont [] v ===> Cret v / (1, 1)

where "c ===> c' / nm" := (Cred c c' nm).

Arguments Mcont S%bind : clear implicits.
Arguments config S%bind : clear implicits.

Inductive steps {S} : config S -> config S -> (nat * nat) -> Prop :=
| steps_zero : forall c,
    steps c c (0,0)
| steps_many : forall c1 c2 c3 n m n' m',
    c1 ===> c2 / (n,m) ->
    steps c2 c3 (n',m') ->
    steps c1 c3 (n+n',m+m').

Definition meta_fill {S} (mk : Mcont S) e :=
  fold_left (λ e k, fill k e) mk e.

(*** Type system *)
(* Type system from "Subtyping Delimited Continuations" (Materzok, Biernacki) *)

Coercion Val : val >-> expr.

Inductive ty :=
| Tnat : ty
| Tarr : ty -> annot -> ty -> ty
| TarrCont : ty -> annot -> ty -> ty
with annot :=
| Aeps : annot
| Acons : ty -> annot -> ty -> annot -> annot
with type := T : ty -> annot -> type.

Declare Custom Entry types.

Notation "[[ t ]]" := t (t custom types at level 2).
Notation "t , s" := (T t s) (in custom types at level 1).

Notation "'N'" := Tnat (in custom types at level 0).
Notation "t --> σ t'" := (Tarr t σ t') (in custom types at level 2, no associativity).
Notation "t '-k>' σ t'" := (TarrCont t σ t') (in custom types at level 2, no associativity).

Notation "'ε'" := Aeps (in custom types at level 0).
Notation "[ t s ] t1 s1" := (Acons t s t1 s1) (in custom types at level 0).
Notation "[ t ] t1 " := (Acons t Aeps t1 Aeps) (in custom types at level 0).

Notation "( t )" := t (in custom types, t at level 2).
Notation "{ t }" := t (in custom types, t constr).
Notation "t" := t (in custom types at level 0, t ident).

Check [[  (N --> [N] N N) , [ N ] N ]].


Inductive sub_ty : ty -> ty -> Prop :=
| sub_nat :
  sub_ty Tnat Tnat
| sub_arr τ1 τ1' τ2 τ2' σ1 σ2 :
  sub_ty τ2' τ1' ->
  sub_type [[τ1, σ1]] [[τ2, σ2]] ->
  sub_ty [[τ1' --> σ1 τ1]] [[τ2' --> σ2 τ2]]
| sub_arr_cont τ1 τ1' τ2 τ2' σ1 σ2 :
  sub_ty τ2' τ1' ->
  sub_type [[τ1, σ1]] [[τ2, σ2]] ->
  sub_ty [[τ1' -k> σ1 τ1]] [[τ2' -k> σ2 τ2]]
with sub_annot : annot -> annot -> Prop :=
| sub_eps_eps :
  sub_annot Aeps Aeps
| sub_eps_cons τ σ τ' σ' :
  sub_type [[τ, σ]] [[τ', σ']] ->
  sub_annot Aeps [[[τ σ] τ' σ']]
| sub_cons τ1 σ1 τ1' σ1' τ2 σ2 τ2' σ2' :
  sub_type [[τ2, σ2]] [[τ1, σ1]] ->
  sub_type [[τ1', σ1']] [[τ2', σ2']] ->
  sub_annot [[[τ1 σ1] τ1' σ1']] [[[τ2 σ2] τ2' σ2']]
with sub_type : type -> type -> Prop :=
| sub_T τ τ' σ σ' :
  sub_ty τ τ' ->
  sub_annot σ σ' ->
  sub_type [[τ, σ]] [[τ', σ']].

Notation "t ≤ t'" := (sub_ty t t') (at level 70).
Notation "s ≤ s'" := (sub_annot s s') (at level 70).
Notation "t ≤ t'" := (sub_type t t') (at level 70).

Reserved Notation "Γ '⊢' e ':' t" (at level 40, e at level 99, no associativity).

Inductive typed {S : Set} (Γ : S -> ty) : expr S -> type -> Prop :=

| typed_sub τ σ τ' σ' e :
  [[τ, σ]] ≤ [[τ', σ']] ->
  Γ ⊢ e : [[τ, σ]] ->
  Γ ⊢ e : [[τ', σ']]

| typed_Lit n :
  Γ ⊢ (LitV n) : [[N, ε]]

| typed_Var (τx : ty) (v : S) :
  Γ v = τx →
  typed Γ (Var v) [[τx, ε]]

| typed_Rec τ1 τ2 σ e :
  (Γ ▹ [[τ1 --> σ τ2]] ▹ τ1) ⊢ e : [[τ2, σ]] ->
  Γ ⊢ (RecV e) : [[(τ1 --> σ τ2), ε]]

| typed_Cont ty k :
  typed_cont Γ k ty ->
  Γ ⊢ (ContV k) : ty

| typed_App (τ1 τ1' τ2 τ2' τ3' τ4' : ty) σ1 σ2 σ3 σ4 f e :
  Γ ⊢ f : [[ (τ1 --> [τ1' σ1] τ4' σ4 τ2) , [τ4' σ4] τ3' σ3 ]] ->
  Γ ⊢ e : [[ τ1 , [τ3' σ3] τ2' σ2]] ->
  Γ ⊢ (App f e) : [[ τ2 , [τ1' σ1] τ2' σ2]]

| typed_AppCont (τ1 τ1' τ2 τ2' τ3' τ4' : ty) σ1 σ2 σ3 σ4 f e :
  Γ ⊢ f : [[ (τ1 -k> [τ1' σ1] τ4' σ4 τ2) , [τ4' σ4] τ3' σ3 ]] ->
  Γ ⊢ e : [[ τ1 , [τ3' σ3] τ2' σ2]] ->
  Γ ⊢ (AppCont f e) : [[ τ2 , [τ1' σ1] τ2' σ2]]

(* | typed_Cont (δ σ τ α : ty) (k : cont S) : *)
(*   typed_cont Γ α k (TarrCont σ α τ α) α -> *)
(*   Γ,δ ⊢ (ContV k) : (TarrCont σ α τ α) , δ *)

(* with typed_cont {S : Set} (Γ : S -> ty) : ty -> cont S -> ty -> ty -> Prop := *)

(* | typed_END τ α δ : *)
(*   typed_cont Γ δ END (TarrCont τ α τ α) δ *)

(* | typed_IfK τ τ' α ε e1 e2 : *)
(*   Γ, α ⊢ e1 : τ, α -> *)
(*   Γ, α ⊢ e2 : τ, α -> *)
(*   typed_cont Γ α K  *)
(*   typed_cont Γ α (IfK e1 e2 K) (TarrCont Tnat ε τ' ε) α *)

(* from the fact that shift k e = shift0 k (reset e) (in the paper) *)
| typed_Shift (e : expr (inc S)) τ1 τ2 σ1 τ3 σ2 τ' τ'' σ'' :
  (Γ ▹ [[τ1 -k> σ1 τ2]]) ⊢ e : [[τ' , [τ' ([τ'' σ''] τ'' σ'')] τ3 σ2]] ->
  Γ ⊢ (Shift e) : [[τ1 , [τ2 σ1] τ3 σ2]]

| typed_Reset e τ τ' τ'' σ'' σ :
  Γ ⊢ e : [[τ' , [τ' ([τ'' σ''] τ'' σ'')] τ σ]] ->
  Γ ⊢ (Reset e) : [[τ, σ]]

with typed_cont {S : Set} (Γ : S -> ty) : cont S -> type -> Prop :=

| typed_end τ :
  typed_cont Γ END [[ (τ -k> ε τ), ε ]]

where "Γ ⊢ e : τ " := (typed Γ e τ).

(* | typed_Val (τ : ty) (v : val S)  : *)
(*   typed_val Γ v τ → *)
(*   typed Γ (Val v) τ *)
(* | typed_Var (τ : ty) (v : S)  : *)
(*   Γ v = τ → *)
(*   typed Γ (Var v) τ *)
(* | typed_App (τ1 τ2 : ty) e1 e2 : *)
(*   typed Γ e1 (Tarr τ1 τ2) → *)
(*   typed Γ e2 τ1 → *)
(*   typed Γ (App e1 e2) τ2 *)
(* | typed_NatOp e1 e2 op : *)
(*   typed Γ e1 Tnat → *)
(*   typed Γ e2 Tnat → *)
(*   typed Γ (NatOp op e1 e2) Tnat *)
(* | typed_If e0 e1 e2 τ : *)
(*   typed Γ e0 Tnat → *)
(*   typed Γ e1 τ → *)
(*   typed Γ e2 τ → *)
(*   typed Γ (If e0 e1 e2) τ *)
(* | typed_Shift (e : expr (inc S)) τ : *)
(*   typed (Γ ▹ Tcont τ) e τ -> *)
(*   typed Γ (Shift e) τ *)
(* | typed_App_Cont (τ τ' : ty) e1 e2 : *)
(*   typed Γ e1 (Tcont τ) -> *)
(*   typed Γ e2 τ -> *)
(*   typed Γ (App e1 e2) τ' *)
(* | type_Reset e τ : *)
(*   typed Γ e τ -> *)
(*   typed Γ (Reset e) τ *)
(* (* CHECK *) *)
(* with typed_val {S : Set} (Γ : S -> ty) : ty -> val S -> ty -> ty -> Prop := *)
(* | typed_Lit n : *)
(*   typed_val Γ (LitV n) Tnat *)
(* | typed_RecV (τ1 τ2 : ty) (e : expr (inc (inc S))) : *)
(*   typed (Γ ▹ (Tarr τ1 τ2) ▹ σ) e τ2 → *)
(*   typed_val Γ (RecV e) (Tarr τ1 τ2) *)
(* . *)

(*** Notations *)

Declare Scope syn_scope.
Delimit Scope syn_scope with syn.


Coercion App : expr >-> Funclass.
(* Coercion AppLK : expr >-> Funclass. *)
(* Coercion AppRK : expr >-> Funclass. *)

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
  __op K op v := cont_compose K (NatOpLK op v END)
  }.

Global Instance OpNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : OpNotation (F S) (nat_op) (cont S) (cont S) := {
  __op e op K := cont_compose K (NatOpRK op (__asSynExpr e) END)
  }.

Class IfNotation (A B C D : Type) := { __if : A -> B -> C -> D }.

Global Instance IfNotationExpr {S : Set} {F G H : Set -> Type} `{AsSynExpr F, AsSynExpr G, AsSynExpr H} : IfNotation (F S) (G S) (H S) (expr S) := {
  __if e₁ e₂ e₃ := If (__asSynExpr e₁) (__asSynExpr e₂) (__asSynExpr e₃)
  }.

Global Instance IfNotationK {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} :
  IfNotation (cont S) (F S) (G S) (cont S) := {
  __if K e₂ e₃ := cont_compose K (IfK (__asSynExpr e₂) (__asSynExpr e₃) END)
  }.


(* Class OutputNotation (A B : Type) := { __output : A -> B }. *)

(* Global Instance OutputNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} : OutputNotation (F S) (expr S) := { *)
(*   __output e := Output (__asSynExpr e) *)
(*   }. *)

(* Global Instance OutputNotationK {S : Set} : OutputNotation (cont S) (cont S) := { *)
(*   __output K := cont_compose K (OutputK END) *)
(*   }. *)

Class ResetNotation (A B : Type) := { __reset : A -> B }.

Global Instance ResetNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} :
  ResetNotation (F S) (expr S) := { __reset e := Reset (__asSynExpr e) }.

(* Global Instance ResetNotationK {S : Set} : ResetNotation (cont S) (cont S) := *)
(*   { __reset K := cont_compose K (ResetK END) }. *)

(* Class ThrowNotation (A B C : Type) := { __throw : A -> B -> C }. *)

(* Global Instance ThrowNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : ThrowNotation (F S) (G S) (expr S) := { *)
(*   __throw e₁ e₂ := Throw (__asSynExpr e₁) (__asSynExpr e₂) *)
(*   }. *)

(* Global Instance ThrowNotationLK {S : Set} {F : Set -> Type} `{AsSynExpr F} : ThrowNotation (cont S) (F S) (cont S) := { *)
(*   __throw K e₂ := ThrowLK K (__asSynExpr e₂) *)
(*   }. *)

(* Global Instance ThrowNotationRK {S : Set} : ThrowNotation (val S) (cont S) (cont S) := { *)
(*   __throw v K := ThrowRK v K *)
(*   }. *)

Class AppNotation (A B C : Type) := { __app : A -> B -> C }.

Global Instance AppNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : AppNotation (F S) (G S) (expr S) := {
  __app e₁ e₂ := App (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance AppNotationLK {S : Set} : AppNotation (cont S) (val S) (cont S) := {
  __app K v := cont_compose K (AppLK v END)
  }.

Global Instance AppNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : AppNotation (F S) (cont S) (cont S) := {
  __app e K := cont_compose K (AppRK (__asSynExpr e) END)
  }.

Class AppContNotation (A B C : Type) := { __app_cont : A -> B -> C }.

Global Instance AppContNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : AppContNotation (F S) (G S) (expr S) := {
  __app_cont e₁ e₂ := AppCont (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance AppContNotationLK {S : Set} : AppContNotation (cont S) (val S) (cont S) := {
  __app_cont K v := cont_compose K (AppContLK v END)
  }.

Global Instance AppContNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : AppContNotation (F S) (cont S) (cont S) := {
  __app_cont e K := cont_compose K (AppContRK (__asSynExpr e) END)
  }.

Notation of_val := Val (only parsing).

Notation "x '⋆' y" := (__app x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '@k' y" := (__app_cont x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '+' y" := (__op x%syn Add y%syn) : syn_scope.
Notation "x '-' y" := (__op x%syn Sub y%syn) : syn_scope.
Notation "x '*' y" := (__op x%syn Mult y%syn) : syn_scope.
Notation "'if' x 'then' y 'else' z" := (__if x%syn y%syn z%syn) : syn_scope.
(* Notation "'output' x" := (__output x%syn) (at level 60) : syn_scope. *)
(* Notation "'throw' e₁ e₂" := (__throw e₁%syn e₂%syn) (at level 60) : syn_scope. *)
Notation "'#' n" := (LitV n) (at level 60) : syn_scope.
(* Notation "'input'" := (Input) : syn_scope. *)
Notation "'rec' e" := (RecV e%syn) (at level 60) : syn_scope.
Notation "'shift/cc' e" := (Shift e%syn) (at level 60) : syn_scope.
Notation "'reset' e" := (Reset e%syn) (at level 60) : syn_scope.
(* Notation "'cont' K" := (ContV K%syn) (at level 60) : syn_scope. *)
Notation "'$' fn" := (set_pure_resolver fn) (at level 60) : syn_scope.
(* Notation "□" := (EmptyK) : syn_scope. *)
Notation "K '⟪' e '⟫'" := (fill K%syn e%syn) (at level 60) : syn_scope.


(* Notation "'lam' e" := (LamV e%syn) (at level 60) : syn_scope. *)

(* Definition LetE {S : Set} (e : expr S) (e' : expr (inc S)) : expr S := *)
(*   App (LamV e') (e). *)

(* Notation "'let_' e₁ 'in' e₂" := (LetE e₁%syn e₂%syn) (at level 60, right associativity) : syn_scope. *)

(* Definition SeqE {S : Set} (e e' : expr S) : expr S := *)
(*   App (LamV (shift e)) e'. *)

(* Notation "e₁ ';;' e₂" := (SeqE e₁%syn e₂%syn) : syn_scope. *)

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Notation "'ℕ'" := (Tnat) (at level 1) : typ_scope.
Notation "A →ₜ B" := (Tarr A%typ B%typ)
                       (right associativity, at level 60) : typ_scope.
(* Notation "A 'Cont'" := (Tcont A%typ) *)
(*                          (at level 60) : typ_scope. *)

Declare Scope typing_scope.
Delimit Scope typing_scope with typing.

Class TypingNotation (A B C : Type) := { __typing : A -> B -> C -> Prop }.

Notation "Γ ⊢ e : τ" := (__typing Γ e%syn τ%typ) (at level 70, e at level 60) : typing_scope.

(* Global Instance TypingNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} : TypingNotation (S -> ty) (F S) ty := { *)
(*     __typing Γ e τ := typed Γ (__asSynExpr e) τ *)
(*   }. *)

(* Global Instance TypingNotationVal {S : Set} : TypingNotation (S -> ty) (val S) ty := { *)
(*     __typing Γ e τ := typed_val Γ e τ *)
(*   }. *)

Module SynExamples.

  Open Scope syn_scope.

  Example test1 : expr (inc ∅) := ($ 0).
  Example test2 : val ∅ := (rec (if ($ 1) then # 1 else # 0)).
  (* Example test21 : val ∅ := (lam (if ($ 0) then # 1 else #0)). *)
  Example test3 : expr ∅ := (shift/cc (rec ($ 0))).
  Example test4 : expr ∅ := ((# 1) + (# 0)).
  Example test5 : val ∅ := (rec (if ($ 1) then # 1 else (($ 0) ⋆ (($ 1) - (# 1))))).
  Example test6 : expr (inc (inc ∅)) := ($ 0) ⋆ ($ 1).
  (* Example test7 : expr ∅ := (let_ ((rec (if ($ 1) then # 1 else (($ 0) ⋆ (($ 1) - (# 1))))) ⋆ (# 5)) in (output ($ 0))). *)

  Open Scope typing_scope.

  (* Example test8 : Prop := (empty_env ⊢ (# 0) : ℕ). *)
End SynExamples.

(* Definition compute_head_step {S} *)
(*   (e : expr S) (K : cont S) : *)
(*   option (expr S * cont S * (nat * nat)) := *)
(*   match e with *)
(*   | (App (Val (RecV e1)) (Val v2)) => *)
(*       Some ((subst (Inc := inc) ((subst (F := expr) (Inc := inc) e1) *)
(*                                    (Val (shift (Inc := inc) v2))) *)
(*                (Val (RecV e1))), K, (1,0)) *)
(*   (* | Input => *) *)
(*   (*     let '(n, σ') := update_input σ in *) *)
(*   (*     Some ((Val (LitV n)), σ', K, (1, 1)) *) *)
(*   (* | Output (Val (LitV n)) => *) *)
(*   (*     (* let := update_output n σ in *) *) *)
(*   (*     Some ((Val (LitV 0)), σ', K, (1, 1)) *) *)
(*   | (NatOp op (Val v1) (Val v2)) => *)
(*       let res := nat_op_interp op v1 v2 in *)
(*       option_rect (fun _ => option _) (fun v3 => Some ((Val v3), K, (0, 0))) None res *)
(*   | (If (Val (LitV n)) e1 e2) => *)
(*       if (decide (0 < n)) *)
(*       then Some (e1, K, (0, 0)) *)
(*       else *)
(*         if (decide (n = 0)) *)
(*         then Some (e2, K, (0, 0)) *)
(*         else None *)
(*   (* | (Shift e) => *) *)
(*   (*     let (Ki, Ko) := shift_context K in *) *)
(*   (*     let f := cont_to_rec Ki in *) *)
(*   (*     Some ((subst (Inc := inc) e (Val f)), Ko, (1, 1)) *) *)
(*   | (Reset (Val v)) => Some (Val v, K, (1, 1)) *)
(*   (* | (Reset (fill E (Shift e))) => None *) *)
(*   | _ => None *)
(*   end. *)
(* (* CHECK *) *)

(* Example test21 : val ∅ := (rec (if ($ 0) then # 1 else #0))%syn. *)


(* Example testc : option (expr (inc ∅) * cont (inc ∅) * (nat * nat)) := *)
(*   (compute_head_step (App (Val test1) (Val $ LitV 5)) []). *)
(* Eval compute in testc. *)


(* Lemma head_step_reflect {S : Set} (e : expr S) (K Ko : cont S) *)
(*   : option_reflect (fun '(e', K', nm) => head_step e K e' K' Ko nm) *)
(*       True *)
(*       (compute_head_step e  K). *)
(* Proof. *)
(*   destruct e; try (by constructor). *)
(*   - destruct e1; try (by constructor). *)
(*     destruct v; try (by constructor). *)
(*     destruct e2; try (by constructor). *)
(*     constructor. *)
(*     constructor. *)
(*   - destruct e1; try (by constructor). *)
(*     destruct e2; try (by constructor). *)
(*     destruct (nat_op_interp op v v0) eqn:Heqn. *)
(*     + simpl; rewrite Heqn. *)
(*       simpl. *)
(*       constructor. *)
(*       by constructor. *)
(*     + simpl; rewrite Heqn. *)
(*       simpl. *)
(*       constructor. *)
(*       constructor. *)
(*   - destruct e1; try (by constructor). *)
(*     destruct v; try (by constructor). *)
(*     simpl. *)
(*     case_match; simpl. *)
(*     + constructor. *)
(*       constructor. *)
(*       assumption. *)
(*     + case_match; simpl. *)
(*       * constructor. *)
(*         constructor. *)
(*         assumption. *)
(*       * constructor. *)
(*         constructor. *)
(*   (* - simpl. *) *)
(*   (*   destruct (update_input σ) eqn:Heqn. *) *)
(*   (*   by do 2 constructor. *) *)
(*   (* - simpl. *) *)
(*   (*   destruct e; try (by constructor). *) *)
(*   (*   destruct v; try (by constructor). *) *)
(*   (*   destruct (update_output n σ) eqn:Heqn. *) *)
(*   (*   by do 2 constructor. *) *)
(*   (* - simpl. *) *)
(*   (*   destruct (shift_context K) as [Ki Ko] eqn:HK. *) *)
(*   (*   constructor. apply ShiftS with Ki =>//=. *) *)
(*   -  simpl. *)
(*      destruct e; try (by constructor). *)
(*      do 2 constructor. *)
(* Qed. *)
