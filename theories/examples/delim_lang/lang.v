From gitrees Require Export prelude.
From stdpp Require Import gmap.
(* From iris.heap_lang Require Import locations. *)
Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

(* Definition loc : Set := locations.loc. *)
(* Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _. *)
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
(* | Alloc (e : expr) : expr *)
(* | Deref (e : expr) : expr *)
(* | Assign (e₁ : expr) (e₂ : expr) : expr *)
with val {X : Set} :=
| LitV (n : nat) : val
| RecV (e : @expr (inc (inc X))) : val
| ContV (k : cont) : val
(* | LocV (l : loc) : val *)
(* | UnitV : val *)
with cont {X : Set} :=
| END : cont
| IfK (e1 : expr) (e2 : expr) : cont -> cont
| AppRK (v : val) : cont -> cont (* v ◻ *)
| AppLK (e : expr) : cont -> cont (* ◻ e *)
| AppContLK (v : val) : cont -> cont (* ◻ v *)
| AppContRK (e : expr) : cont -> cont (* e ◻ *)
| NatOpLK (op : nat_op) (v : val) : cont -> cont (* ◻ + v *)
| NatOpRK (op : nat_op) (e : expr) : cont -> cont (* e + ◻ *)
(* | AllocK : cont → cont *)
(* | DerefK : cont → cont *)
(* | AssignRK (e : expr) : cont → cont (* E <- e *) *)
(* | AssignLK (v : val) : cont → cont (* v <- E *) *)
.
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
  (* | Alloc e => Alloc (emap f e) *)
  (* | Deref e => Deref (emap f e) *)
  (* | Assign e₁ e₂ => Assign (emap f e₁) (emap f e₂) *)
  end
with
vmap {A B : Set} (f : A [→] B) (v : val A) : val B :=
  match v with
  | LitV n => LitV n
  | RecV e => RecV (emap ((f ↑) ↑) e)
  | ContV k => ContV (kmap f k)
  (* | LocV l => LocV l *)
  (* | UnitV => UnitV *)
  end
with kmap {A B : Set} (f : A [→] B) (K : cont A) : cont B :=
   match K with
   | END => END
   | IfK e1 e2 k => IfK (emap f e1) (emap f e2) (kmap f k)
   | AppLK v k => AppLK (emap f v) (kmap f k)
   | AppRK e k => AppRK (vmap f e) (kmap f k)
   | AppContLK v k => AppContLK (vmap f v) (kmap f k)
   | AppContRK e k => AppContRK (emap f e) (kmap f k)
   | NatOpLK op v k => NatOpLK op (vmap f v) (kmap f k)
   | NatOpRK op e k => NatOpRK op (emap f e) (kmap f k)
   (* | AllocK k => AllocK (kmap f k) *)
   (* | DerefK k => DerefK (kmap f k) *)
   (* | AssignRK e k => AssignRK (emap f e) (kmap f k) *)
   (* | AssignLK v k => AssignLK (vmap f v) (kmap f k) *)
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
  (* | Alloc e => Alloc (ebind f e) *)
  (* | Deref e => Deref (ebind f e) *)
  (* | Assign e₁ e₂ => Assign (ebind f e₁) (ebind f e₂) *)
  end
with
vbind {A B : Set} (f : A [⇒] B) (v : val A) : val B :=
  match v with
  | LitV n => LitV n
  | RecV e => RecV (ebind ((f ↑) ↑) e)
  | ContV k => ContV (kbind f k)
  (* | LocV l => LocV l *)
  (* | UnitV => UnitV *)
  end
with kbind {A B : Set} (f : A [⇒] B) (K : cont A) : cont B :=
   match K with
   | END => END
   | IfK e1 e2 k => IfK (ebind f e1) (ebind f e2) (kbind f k)
   | AppLK v k => AppLK (ebind f v) (kbind f k)
   | AppRK e k => AppRK (vbind f e) (kbind f k)
   | AppContLK v k => AppContLK (vbind f v) (kbind f k)
   | AppContRK e k => AppContRK (ebind f e) (kbind f k)
   | NatOpLK op v k => NatOpLK op (vbind f v) (kbind f k)
   | NatOpRK op e k => NatOpRK op (ebind f e) (kbind f k)
   (* | AllocK k => AllocK (kbind f k) *)
   (* | DerefK k => DerefK (kbind f k) *)
   (* | AssignRK e k => AssignRK (ebind f e) (kbind f k) *)
   (* | AssignLK v k => AssignLK (vbind f v) (kbind f k) *)
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
  | AppRK v K => fill K (App (Val v) e)
  | AppLK el K => fill K (App e el)
  | AppContLK v K => fill K (AppCont e (Val v))
  | AppContRK el K => fill K (AppCont el e)
  | NatOpLK op v K => fill K (NatOp op e (Val v))
  | NatOpRK op el K => fill K (NatOp op el e)
  (* | AllocK K => fill K (Alloc e) *)
  (* | DerefK K => fill K (Deref e) *)
  (* | AssignRK e' K => fill K (Assign e e') *)
  (* | AssignLK v K => fill K (Assign (Val v) e) *)
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
  | AppLK e K => AppLK e (cont_compose K1 K)
  | AppRK v K => AppRK v (cont_compose K1 K)
  | AppContLK v K => AppContLK v (cont_compose K1 K)
  | AppContRK e K => AppContRK e (cont_compose K1 K)
  | NatOpLK op v K => NatOpLK op v (cont_compose K1 K)
  | NatOpRK op e K => NatOpRK op e (cont_compose K1 K)
  (* | AllocK K => AllocK (cont_compose K1 K) *)
  (* | DerefK K => DerefK (cont_compose K1 K) *)
  (* | AssignRK e' K => AssignRK e' (cont_compose K1 K) *)
  (* | AssignLK v K => AssignLK v (cont_compose K1 K) *)
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
(* Definition state X := gmap loc (val X). *)

Variant config {S} : Type :=
  | Ceval : expr S -> cont S -> @Mcont S → config
  | Ccont : cont S -> val S -> @Mcont S -> config
  | Cmcont : @Mcont S -> val S -> config
  | Cexpr : expr S -> config
  | Cret : val S -> config.

Reserved Notation "c '===>' c' / nm"
  (at level 40, c', nm at level 30).

Variant Cred {S : Set} : config (* * state S *) -> config (* * state S *)
                         -> (nat * nat) -> Prop :=
(* init *)
| Ceval_init : forall (e : expr S) (* σ *),
  (Cexpr e(* , σ *)) ===> (Ceval e END [](* , σ *)) / (0,0)

(* eval *)
| Ceval_val : forall v k mk (* σ *),
  (Ceval (Val v) k mk(* , σ *)) ===> (Ccont k v mk(* , σ *)) / (0,0)

| Ceval_app : forall e0 e1 k mk (* σ *),
  (Ceval (App e0 e1) k mk(* , σ *)) ===> (Ceval e0 (AppLK e1 k) mk(* , σ *)) / (0,0)

| Ceval_app_cont : forall e0 e1 k mk (* σ *),
  (Ceval (AppCont e0 e1) k mk(* , σ *)) ===> (Ceval e1 (AppContRK e0 k) mk(* , σ *)) / (0,0)

| Ceval_natop : forall op e0 e1 k mk (* σ *),
  (Ceval (NatOp op e0 e1) k mk(* , σ *)) ===> (Ceval e1 (NatOpRK op e0 k) mk(* , σ *)) / (0,0)

| Ceval_if : forall eb et ef k mk (* σ *),
  (Ceval (If eb et ef) k mk(* , σ *)) ===> (Ceval eb (IfK et ef k) mk(* , σ *)) / (0,0)

| Ceval_reset : forall e k mk (* σ *),
  (Ceval (Reset e) k mk(* , σ *)) ===> (Ceval e END (k :: mk)(* , σ *)) / (1, 1)

| Ceval_shift : forall (e : expr $ inc S) k mk (* σ *),
  (Ceval (Shift e) k mk(* , σ *)) ===>
    (Ceval (subst (Inc := inc) e (Val $ ContV k)) END mk(* , σ *)) / (1, 1)

(* cont *)
| Ccont_end : forall v mk (* σ *),
  (Ccont END v mk(* , σ *)) ===> (Cmcont mk v(* , σ *)) / (0,0)

| Ccont_appl : forall e v k mk (* σ *),
  (Ccont (AppLK e k) v mk(* , σ *)) ===> (Ceval e (AppRK v k) mk(* , σ *)) / (0, 0)

| Ccont_app_contr : forall e v k mk (* σ *),
  (Ccont (AppContRK e k) v mk(* , σ *)) ===> (Ceval e (AppContLK v k) mk(* , σ *)) / (0, 0)

| Ccont_appr : forall e v k mk (* σ *),
  (Ccont (AppRK (RecV e) k) v mk(* , σ *)) ===>
    (Ceval (subst (Inc := inc)
              (subst (F := expr) (Inc := inc) e
                 (Val (shift (Inc := inc) v)))
              (Val (RecV e))) k mk(* , σ *)) / (1, 0)

| Ccont_cont : forall v k k' mk (* σ *),
  (Ccont (AppContLK v k) (ContV k') mk(* , σ *)) ===>
    (Ccont k' v (k :: mk)(* , σ *)) / (2, 1)

| Ccont_if : forall et ef n k mk (* σ *),
  (Ccont (IfK et ef k) (LitV n) mk(* , σ *)) ===>
    (Ceval (if (n =? 0) then ef else et) k mk(* , σ *)) / (0, 0)

| Ccont_natopr : forall op e v k mk (* σ *),
  (Ccont (NatOpRK op e k) v mk(* , σ *)) ===>
    (Ceval e (NatOpLK op v k) mk(* , σ *)) / (0, 0)

| Ccont_natopl : forall op v0 v1 v2 k mk (* σ *),
  nat_op_interp op v0 v1 = Some v2 ->
  (Ccont (NatOpLK op v1 k) v0 mk(* , σ *)) ===>
    (Ceval (Val v2) k mk(* , σ *)) / (0,0)

(* meta-cont *)
| Cmcont_cont : forall k mk v (* σ *),
  (Cmcont (k :: mk) v(* , σ *)) ===> (Ccont k v mk(* , σ *)) / (1,1)

| Cmcont_ret : forall v (* σ *),
  (Cmcont [] v(* , σ *)) ===> (Cret v(* , σ *)) / (1, 1)

(* | Ceval_assign : forall e0 e1 k mk σ, *)
(*   (Ceval (Assign e0 e1) k mk, σ) ===> (Ceval e1 (AssignRK e0 k) mk, σ) / (0, 0) *)

(* | Ccont_assignr : forall e v k mk σ, *)
(*   (Ccont (AssignRK e k) v mk, σ) ===> (Ceval e (AssignLK v k) mk, σ) / (0, 0) *)

(* | Ccont_assignl : forall l v' k mk σ, *)
(*   (Ccont (AssignLK (LocV l) k) v' mk, σ) ===> *)
(*     (Ceval (Val UnitV) k mk, <[l:=v']>σ) / (0, 1) *)

(* | Ceval_alloc : forall e k mk σ, *)
(*   (Ceval (Alloc e) k mk, σ) ===> (Ceval e (AllocK k) mk, σ) / (0, 0) *)

(* | Ceval_allock : ∀ l v k mk σ, *)
(*   σ !! l = None -> *)
(*   (Ccont (AllocK k) v mk, σ) ===> *)
(*     (Ceval (Val (LocV l)) k mk, <[l:=v]>σ) / (0, 1) *)

(* | Ceval_deref : forall e k mk σ, *)
(*   (Ceval (Deref e) k mk, σ) ===> (Ceval e (DerefK k) mk, σ) / (0, 0) *)

(* | Ceval_derefk : ∀ l v k mk σ, *)
(*   σ !! l = Some v -> *)
(*   (Ccont (DerefK k) (LocV l) mk, σ) ===> *)
(*     (Ceval (Val v) k mk, σ) / (0, 1) *)
where "c ===> c' / nm" := (Cred c c' nm).

Arguments Mcont S%bind : clear implicits.
Arguments config S%bind : clear implicits.

Inductive steps {S} : config S (* * state S *) -> config S (* * state S *) -> (nat * nat) -> Prop :=
| steps_zero : forall c,
  steps c c (0, 0)
| steps_many : forall c1 c2 c3 n m n' m' n'' m'',
  n'' = n + n' -> m'' = m + m' ->
  c1 ===> c2 / (n, m) ->
  steps c2 c3 (n', m') ->
  steps c1 c3 (n'', m'').

Definition meta_fill {S} (mk : Mcont S) e :=
  fold_left (λ e k, fill k e) mk e.

Coercion Val : val >-> expr.

(*** Notations *)

Declare Scope syn_scope.
Delimit Scope syn_scope with syn.

(* Coercion LocV : loc >-> val. *)
Coercion App : expr >-> Funclass.

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

Class ResetNotation (A B : Type) := { __reset : A -> B }.

Global Instance ResetNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} :
  ResetNotation (F S) (expr S) := { __reset e := Reset (__asSynExpr e) }.

Class AppNotation (A B C : Type) := { __app : A -> B -> C }.

Global Instance AppNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : AppNotation (F S) (G S) (expr S) := {
  __app e₁ e₂ := App (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance AppNotationRK {S : Set} : AppNotation (cont S) (val S) (cont S) := {
  __app K v := cont_compose K (AppRK v END)
  }.

Global Instance AppNotationLK {S : Set} {F : Set -> Type} `{AsSynExpr F} : AppNotation (F S) (cont S) (cont S) := {
  __app e K := cont_compose K (AppLK (__asSynExpr e) END)
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

(* Class AllocNotation (A B : Type) := { __alloc : A -> B }. *)
(* Notation "'alloc' e" := (__alloc e%syn) (at level 61) : syn_scope. *)

(* Global Instance AllocNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} : *)
(*   AllocNotation (F S) (expr S) := { __alloc e := Alloc (__asSynExpr e) }. *)

(* Global Instance AllocNotationK {S : Set} : AllocNotation (cont S) (cont S) := *)
(*   { __alloc K := AllocK K }. *)

(* Class DerefNotation (A B : Type) := { __deref : A -> B }. *)
(* Notation "'!' e" := (__deref e%syn) (at level 61) : syn_scope. *)

(* Global Instance DerefNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} : *)
(*   DerefNotation (F S) (expr S) := { __deref e := Deref (__asSynExpr e) }. *)

(* Global Instance DerefNotationK {S : Set} : DerefNotation (cont S) (cont S) := *)
(*   { __deref K := DerefK K }. *)

(* Class AssignNotation (A B C : Type) := { __assign : A -> B -> C }. *)
(* (* <- !!! *) *)
(* Notation "x '<-' y" := (__assign x%syn y%syn) *)
(*                         (at level 40, y at next level, left associativity) *)
(*     : syn_scope. *)

(* Global Instance AssignNotationExpr {S : Set} {F G : Set -> Type} *)
(*   `{AsSynExpr F, AsSynExpr G} : AssignNotation (F S) (G S) (expr S) := { *)
(*   __assign e₁ e₂ := Assign (__asSynExpr e₁) (__asSynExpr e₂) *)
(*   }. *)

(* Global Instance AssignNotationLK {S : Set} *)
(*   : AssignNotation (cont S) (val S) (cont S) := { *)
(*     __assign K v := AssignLK v K *)
(*   }. *)

(* Global Instance AssignNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} *)
(*   : AssignNotation (F S) (cont S) (cont S) := { *)
(*     __assign e K := AssignRK (__asSynExpr e) K *)
(*   }. *)

Notation of_val := Val (only parsing).

Notation "x '⋆' y" := (__app x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '@k' y" := (__app_cont x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '+' y" := (__op x%syn Add y%syn) : syn_scope.
Notation "x '-' y" := (__op x%syn Sub y%syn) : syn_scope.
Notation "x '*' y" := (__op x%syn Mult y%syn) : syn_scope.
Notation "'if' x 'then' y 'else' z" := (__if x%syn y%syn z%syn) : syn_scope.
Notation "'#' n" := (LitV n) (at level 60) : syn_scope.
Notation "'rec' e" := (RecV e%syn) (at level 60) : syn_scope.
Notation "'shift/cc' e" := (Shift e%syn) (at level 60) : syn_scope.
Notation "'reset' e" := (Reset e%syn) (at level 60) : syn_scope.
Notation "'$' fn" := (set_pure_resolver fn) (at level 60) : syn_scope.
Notation "K '⟪' e '⟫'" := (fill K%syn e%syn) (at level 60) : syn_scope.

Module SynExamples.

  Open Scope syn_scope.

  Example test1 : expr (inc ∅) := $0.
  Example test2 : expr (inc (inc ∅)) := ($0) ⋆ $1.
  Example test3 : expr ∅ := (rec (reset (shift/cc (($0) @k $1)))).
  Example test4 : expr ∅ :=
    (rec (if ($0) then #1 else (($0) ⋆ (($0) - #1)))).
  (* Example test5 : expr ∅ := *)
  (*   ((alloc #1) <- #2). *)
  (* Example test6 : expr ∅ := *)
  (*   (! alloc #1). *)
  (* Example test7 : *)
  (*   (∃ (ℓ : loc), *)
  (*      steps (Cexpr (! alloc #1), empty) (Cret (#1 : val ∅), <[ℓ:=#1]>∅%stdpp) (1, 3)). *)
  (* Proof. *)
  (*   set (ℓ := (fresh (dom (∅%stdpp : state ∅)))). *)
  (*   exists ℓ. *)
  (*   eapply steps_many with _ 0 0 1 3; first reflexivity; first reflexivity; *)
  (*     first apply Ceval_init. *)
  (*   eapply steps_many with _ _ _ 1 3; [| | apply Ceval_deref |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   eapply steps_many with _ _ _ 1 3; [| | apply Ceval_alloc |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   eapply steps_many with _ _ _ 1 3; [| | apply Ceval_val |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   eapply steps_many with _ _ _ 1 2; [| | apply (Ceval_allock ℓ) |]; *)
  (*     first reflexivity; first reflexivity; first set_solver. *)
  (*   eapply steps_many with _ _ _ 1 2; [| | apply Ceval_val |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   eapply steps_many with _ _ _ 1 _; [| | eapply (Ceval_derefk ℓ (LitV 1)) |]; *)
  (*     first reflexivity; first reflexivity; first set_solver. *)
  (*   eapply steps_many with _ _ _ 1 1; [| | apply Ceval_val |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   eapply steps_many with _ _ _ 1 1; [| | apply Ccont_end |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   eapply steps_many with _ _ _ 0 0; [| | apply Cmcont_ret |]; *)
  (*     first reflexivity; first reflexivity. *)
  (*   apply steps_zero. *)
  (* Qed. *)
  Example test8 : expr (inc ∅) := ($ 0).
  Example test9 : val ∅ := (rec (if ($ 1) then # 1 else # 0)).
  Example test10 : expr ∅ := (shift/cc (rec ($ 0))).
  Example test11 : expr ∅ := ((# 1) + (# 0)).
  Example test12 : val ∅ := (rec (if ($ 1) then # 1 else (($ 0) ⋆ (($ 1) - (# 1))))).
  Example test13 : expr (inc (inc ∅)) := ($ 0) ⋆ ($ 1).
End SynExamples.
