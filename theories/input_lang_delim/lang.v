From stdpp Require Export strings.
From gitrees Require Export prelude.
(* From Equations Require Import Equations. *)
Require Import List.
Import ListNotations.

Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

Require Import FunctionalExtensionality.


Variant nat_op := Add | Sub | Mult.

Inductive expr {X : Set} :=
(* Values *)
| Val (v : val) : expr
| Var (x : X) : expr
(* Base lambda calculus *)
| App (e₁ : expr) (e₂ : expr) : expr
(* Base types and their operations *)
| NatOp (op : nat_op) (e₁ : expr) (e₂ : expr) : expr
| If (e₁ : expr) (e₂ : expr) (e₃ : expr) : expr
(* The effects *)
| Input : expr
| Output (e : expr) : expr
| Shift (e : @expr (inc X)) : expr
| Reset (e : expr) : expr
with val {X : Set} :=
| LitV (n : nat) : val
| RecV (e : @expr (inc (inc X))) : val.



Variant ectx_el {X : Set} :=
  | OutputK : ectx_el
  | IfCondK (e1 : @expr X) (e2 : @expr X) : ectx_el
  | IfTrueK (b : @expr X) (e2 : @expr X) : ectx_el
  | IfFalseK (b : @expr X) (e1 : @expr X) : ectx_el
  | AppLK (er : @expr X) : ectx_el (* ◻ er *)
  | AppRK (el : @expr X) : ectx_el (* el ◻ *)
  | NatOpLK (op : nat_op) (er : @expr X) : ectx_el (* ◻ + er *)
  | NatOpRK (op : nat_op) (el : @expr X) : ectx_el (* el + square *)
  | ResetK : ectx_el.


Definition ectx {X : Set} := list (@ectx_el X).

Arguments val X%bind : clear implicits.
Arguments expr X%bind : clear implicits.
Arguments ectx_el X%bind : clear implicits.
Arguments ectx X%bind : clear implicits.




Local Open Scope bind_scope.


Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vmap f v)
  | Var x => Var (f x)
  | App e₁ e₂ => App (emap f e₁) (emap f e₂)
  | NatOp o e₁ e₂ => NatOp o (emap f e₁) (emap f e₂)
  | If e₁ e₂ e₃ => If (emap f e₁) (emap f e₂) (emap f e₃)
  | Input => Input
  | Output e => Output (emap f e)
  | Shift e => Shift (emap (f ↑) e)
  | Reset e => Reset (emap f e)
  end
with
vmap {A B : Set} (f : A [→] B) (v : val A) : val B :=
  match v with
  | LitV n => LitV n
  | RecV e => RecV (emap ((f ↑) ↑) e)
(* | ContV K => ContV (kmap f K) *)
  end.

#[export] Instance FMap_expr : FunctorCore expr := @emap.
#[export] Instance FMap_val  : FunctorCore val := @vmap.

Definition kmap {A B : Set} (f : A [→] B) (K : ectx A) : ectx B :=
  map (fun x => match x with
              | OutputK => OutputK
              | IfCondK e1 e2 => IfCondK (fmap f e1) (fmap f e2)
              | IfTrueK b e2 => IfTrueK (fmap f b) (fmap f e2)
              | IfFalseK b e1 => IfFalseK (fmap f b) (fmap f e1)
              | AppLK er => AppLK (fmap f er)
              | AppRK el => AppRK (fmap f el)
              | NatOpLK op er => NatOpLK op (fmap f er)
              | NatOpRK op el => NatOpRK op (fmap f el)
              | ResetK => ResetK
              end) K.

#[export] Instance FMap_ectx  : FunctorCore ectx := @kmap.

#[export] Instance SPC_expr : SetPureCore expr := @Var.

Fixpoint ebind {A B : Set} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | Val v => Val (vbind f v)
  | Var x => f x
  | App e₁ e₂ => App (ebind f e₁) (ebind f e₂)
  | NatOp o e₁ e₂ => NatOp o (ebind f e₁) (ebind f e₂)
  | If e₁ e₂ e₃ => If (ebind f e₁) (ebind f e₂) (ebind f e₃)
  | Input => Input
  | Output e => Output (ebind f e)
  | Shift e => Shift (ebind (f ↑) e)
  | Reset e => Reset (ebind f e)
  end
with
vbind {A B : Set} (f : A [⇒] B) (v : val A) : val B :=
  match v with
  | LitV n => LitV n
  | RecV e => RecV (ebind ((f ↑) ↑) e)
  (* | ContV K => ContV (kbind f K) *)
  end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.
#[export] Instance BindCore_val  : BindCore val := @vbind.

Definition kbind {A B : Set} (f : A [⇒] B) (K : ectx A) : ectx B :=
  map (fun x => match x with
              | OutputK => OutputK
              | IfCondK e1 e2 => IfCondK (bind f e1) (bind f e2)
              | IfTrueK b e2 => IfTrueK (bind f b) (bind f e2)
              | IfFalseK b e1 => IfFalseK (bind f b) (bind f e1)
              | AppLK er => AppLK (bind f er)
              | AppRK el => AppRK (bind f el)
              | NatOpLK op er => NatOpLK op (bind f er)
              | NatOpRK op el => NatOpRK op (bind f el)
              | ResetK => ResetK
              end) K.

(* with kbind {A B : Set} (f : A [⇒] B) (K : ectx A) : ectx B := *)
(*        match K with *)
(*        | EmptyK => EmptyK *)
(*        | OutputK K => OutputK (kbind f K) *)
(*        | IfK K e₁ e₂ => IfK (kbind f K) (ebind f e₁) (ebind f e₂) *)
(*        | AppLK K v => AppLK (kbind f K) (vbind f v) *)
(*        | AppRK e K => AppRK (ebind f e) (kbind f K) *)
(*        | NatOpRK op e K => NatOpRK op (ebind f e) (kbind f K) *)
(*        | NatOpLK op K v => NatOpLK op (kbind f K) (vbind f v) *)
(*        | ResetK K => ResetK (kbind f K) *)
(*        end. *)

#[export] Instance BindCore_ectx  : BindCore ectx := @kbind.

#[export] Instance IP_typ : SetPure expr.
Proof.
  split; intros; reflexivity.
Qed.

Fixpoint vmap_id X (δ : X [→] X) (v : val X) : δ ≡ ı → fmap δ v = v
with emap_id X (δ : X [→] X) (e : expr X) : δ ≡ ı → fmap δ e = e.
(* with kmap_id X (δ : X [→] X) (e : ectx X) : δ ≡ ı → fmap δ e = e. *)
Proof.
  - auto_map_id.
  - auto_map_id.
Qed.

Definition kmap_id X (δ : X [→] X) (k : ectx X) : δ ≡ ı -> fmap δ k = k.
Proof.
  rewrite  /fmap /FMap_ectx /kmap => H.
  rewrite <-List.map_id. do 2 f_equal.
  extensionality x. case: x => // >; rewrite !emap_id//.
Qed.


Fixpoint vmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (v : val A) :
  f ∘ g ≡ h → fmap f (fmap g v) = fmap h v
with emap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : expr A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e.
Proof.
  - auto_map_comp.
  - auto_map_comp.
Qed.


Definition kmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : ectx A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e.
Proof.
  rewrite  /fmap /FMap_ectx => H.
  rewrite /kmap map_map. do 2 f_equal.
  extensionality x.
  case : x => // >; rewrite !(emap_comp _ _ _ f g h)//.
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
  f ̂ ≡ g → fmap f e = bind g e.
Proof.
  - auto_map_bind_pure.
    erewrite emap_ebind_pure; [reflexivity |].
    intros [| [| x]]; term_simpl; [reflexivity | reflexivity |].
    rewrite <-(EQ x).
    reflexivity.
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

Definition kmap_kbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : ectx A) :
  f ̂ ≡ g → fmap f e = bind g e.
Proof.
  rewrite /fmap /FMap_ectx /bind /BindCore_ectx /kmap /kbind => H.
  do 2 f_equal. extensionality x.
  case: x => [] > //; rewrite !(emap_ebind_pure _ _ _ g)//.
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
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e).
Proof.
  - auto_map_bind_comm.
    erewrite emap_ebind_comm; [reflexivity |].
    erewrite lift_comm; [reflexivity |].
    erewrite lift_comm; [reflexivity | assumption].
  - auto_map_bind_comm.
Qed.

Definition kmap_kbind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
       (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (e : ectx A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e).
Proof.
  rewrite /fmap /FMap_ectx /bind /BindCore_ectx /kmap /kbind => H.
  rewrite !map_map. do 2 f_equal. extensionality x.
  case : x => // >; rewrite !(emap_ebind_comm _ B₁ _ _ f₁ _ g₁)//.
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
  f ≡ ı → bind f e = e.
Proof.
  - auto_bind_id.
    rewrite ebind_id; [reflexivity |].
    apply lift_id, lift_id; assumption.
  - auto_bind_id.
Qed.

Definition kbind_id  (A : Set) (f : A [⇒] A) (e : ectx A) :
  f ≡ ı → bind f e = e.
Proof.
  rewrite /bind /BindCore_ectx /kbind => H.
  rewrite <-List.map_id. do 2 f_equal.
  extensionality x. case : x => // >; rewrite !ebind_id//.
Qed.



Fixpoint vbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (v : val A) :
  f ∘ g ≡ h → bind f (bind g v) = bind h v
with ebind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : expr A) :
  f ∘ g ≡ h → bind f (bind g e) = bind h e.
Proof.
  - auto_bind_comp.
    erewrite ebind_comp; [reflexivity |].
    erewrite lift_comp; [reflexivity |].
    erewrite lift_comp; [reflexivity | assumption].
  - auto_bind_comp.
Qed.

Definition kbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : ectx A) :
  f ∘ g ≡ h → bind f (bind g e) = bind h e.
Proof.
  rewrite /bind/BindCore_ectx/kbind => H.
  rewrite map_map. do 2 f_equal. extensionality x.
  case : x => // >; rewrite !(ebind_comp _ _ _ _ _ h)//.
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



Definition LamV {S : Set} (e : expr (inc S)) : val S :=
  RecV (shift e).


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


Definition ctx_el_to_expr {X : Set} (K : ectx_el X) (e : expr X) : expr X :=
  match K with
  | OutputK => Output $ e
  | IfCondK e1 e2 => If e e1 e2
  | IfTrueK b e2 => If b e e2
  | IfFalseK b e1 => If b e1 e
  | AppLK er => App e er
  | AppRK el => App el e
  | NatOpLK op er => NatOp op e er
  | NatOpRK op el => NatOp op el e
  | ResetK => Reset e
  end.

Definition fill {X : Set} (K : ectx X) (e : expr X) : expr X :=
  fold_left (fun e c => ctx_el_to_expr c e) K e.


Fixpoint trim_to_first_reset {X : Set} (K : ectx X) (acc : ectx X) : (ectx X * ectx X) :=
  match K with
  | OutputK :: K => trim_to_first_reset K (OutputK :: acc)
  | (IfCondK e1 e2) :: K => trim_to_first_reset K ((IfCondK e1 e2) :: acc)
  | (IfTrueK b e2) :: K => trim_to_first_reset K ((IfTrueK b e2) :: acc)
  | (IfFalseK b e1) :: K => trim_to_first_reset K ((IfFalseK b e1) :: acc)
  | (AppLK er) :: K => trim_to_first_reset K ((AppLK er) :: acc)
  | (AppRK el) :: K => trim_to_first_reset K ((AppRK el) :: acc)
  | (NatOpLK op er) :: K => trim_to_first_reset K ((NatOpLK op er) :: acc)
  | (NatOpRK op el) :: K => trim_to_first_reset K ((NatOpRK op el) :: acc)
  | (ResetK) :: K => (acc, ResetK :: K)
  | [] => (acc, [])
  end.

(* Separate continuation [K] on innermost [reset] *)
Definition shift_context {X : Set} (K : ectx X) : (ectx X * ectx X) :=
  let (Ki, Ko) := trim_to_first_reset K [] in
  (List.rev Ki, Ko).


(* Only if no reset in K *)
Definition cont_to_rec {X : Set} (K : ectx X) : (val X) :=
  LamV (fill (shift K) (Var VZ)).


(* Lemma fill_emap {X Y : Set} (f : X [→] Y) (K : ectx X) (e : expr X) *)
(*   : fmap f (fill K e) = fill (fmap f K) (fmap f e). *)
(* Proof. *)
(*   revert f. *)
(*   induction K as *)
(*     [ | ?? IH | ?? IH | ?? IH | ??? IH | ???? IH *)
(*     | ??? IH | ?? IH ]; *)
(*     intros f; term_simpl; first done; rewrite IH; reflexivity. *)
(* Qed. *)

(*** Operational semantics *)

Record state := State {
                   inputs : list nat;
                   outputs : list nat;
                 }.
#[export] Instance state_inhabited : Inhabited state := populate (State [] []).

Definition update_input (s : state) : nat * state :=
  match s.(inputs) with
  | [] => (0, s)
  | n::ns =>
      (n, {| inputs := ns; outputs := s.(outputs) |})
  end.
Definition update_output (n:nat) (s : state) : state :=
  {| inputs := s.(inputs); outputs := n::s.(outputs) |}.


(** [head_step e σ K e' σ' K' (n, m)] : step from [(e, σ, K)] to [(e', σ', K')] 
    in [n] ticks with [m] effects encountered *)
Variant head_step {S} : expr S → state -> ectx S →
                        expr S → state → ectx S →
                        nat * nat → Prop :=
  | BetaS e1 v2 σ K :
    head_step (App (Val $ RecV e1) (Val v2)) σ K
      (subst (Inc := inc) ((subst (F := expr) (Inc := inc) e1)
                             (Val (shift (Inc := inc) v2)))
         (Val (RecV e1))) σ K (1,0)
  | InputS σ n σ' K :
    update_input σ = (n, σ') →
    head_step Input σ K (Val (LitV n)) σ' K (1, 1)
  | OutputS σ n σ' K :
    update_output n σ = σ' →
    head_step (Output (Val (LitV n))) σ K (Val (LitV 0)) σ' K (1, 1)
  | NatOpS op v1 v2 v3 σ K :
    nat_op_interp op v1 v2 = Some v3 →
    head_step (NatOp op (Val v1) (Val v2)) σ K
      (Val v3) σ K (0, 0)
  | IfTrueS n e1 e2 σ K :
    n > 0 →
    head_step (If (Val (LitV n)) e1 e2) σ K
      e1 σ K (0, 0)
  | IfFalseS n e1 e2 σ K :
    n = 0 →
    head_step (If (Val (LitV n)) e1 e2) σ K
      e2 σ K (0, 0)

  | ShiftS e σ K Ki Ko f:
    ((Ki, Ko) = shift_context K) ->
    f = cont_to_rec Ki ->
    head_step (Shift e) σ K (subst (Inc := inc) e (Val f)) σ Ko (1, 1)

  | ResetS v σ K :
    head_step (Reset (Val v)) σ K (Val v) σ K (1, 1).


  (* | ValueS v σ K C: *)
  (*   head_step (Val v) σ (C::K) (ctx_el_to_expr C (Val v)) σ K (0, 0) *)

  (* | ResetShiftS e σ K E: *)
  (*   head_step *)
  (*     (Reset (fill E (Shift e))) σ *)
  (*     (Reset (subst (Inc := inc) e (Val $ ContV $ ResetK E))) σ K (1,0). *)

Lemma head_step_io_01 {S} (e1 e2 : expr S) σ1 σ2 K K' n m :
  head_step e1 σ1 K e2 σ2 K' (n,m) → m = 0 ∨ m = 1.
Proof.  inversion 1; eauto. Qed.
Lemma head_step_unfold_01 {S} (e1 e2 : expr S) σ1 σ2 K K' n m :
  head_step e1 σ1 K e2 σ2 K' (n,m) → n = 0 ∨ n = 1.
Proof.  inversion 1; eauto. Qed.
Lemma head_step_no_io {S} (e1 e2 : expr S) σ1 σ2 K K' n :
  head_step e1 σ1 K e2 σ2 K' (n,0) → σ1 = σ2.
Proof.  inversion 1; eauto. Qed.

(** Carbonara from heap lang *)

Global Instance ctx_el_to_expr_inj {S} (C : ectx_el S) : Inj (=) (=) (ctx_el_to_expr C).
Proof. case: C => [] >; simpl in*; congruence. Qed.

Global Instance fill_inj {S} (Ki : ectx S) : Inj (=) (=) (fill Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma ctx_el_to_expr_val {S} C (e : expr S) :
  is_Some (to_val (ctx_el_to_expr C e)) → is_Some (to_val e).
Proof. case : C => [] > H; simpl in H; try by apply is_Some_None in H. Qed.

Lemma fill_val {S} Ki (e : expr S) :
  is_Some (to_val (fill Ki e)) → is_Some (to_val e).
Proof. elim: Ki e; simpl in *; first done. intros.
       apply (ctx_el_to_expr_val a e). apply H. apply H0.
Qed.

(* CHECK *)
(* Lemma val_head_stuck {S} (e1 : expr S) σ1 e2 σ2 K m : *)
(*   head_step e1 σ1 e2 σ2 K m → to_val e1 = None. *)
(* Proof. destruct 1; naive_solver. Qed. *)


(* K1 ∘ K2 *)
Definition ectx_compose {S} (K1 K2 : ectx S) : ectx S :=
  K2 ++ K1.

Lemma fill_app {S} (K1 K2 : ectx S) e : fill (ectx_compose K1 K2) e = fill K1 (fill K2 e).
Proof.
  elim: K2 K1 e =>>; eauto.
  intros H K1 e. simpl. by rewrite H.
Qed.


Lemma fill_not_val : ∀ {S} K (e : expr S), to_val e = None → to_val (fill K e) = None.
Proof.
  intros S K e. rewrite !eq_None_not_Some.
  eauto using fill_val.
Qed.


Lemma fill_comp {S} K1 K2 (e : expr S) : fill K2 (fill K1 e) = fill (ectx_compose K2 K1) e.
Proof. by rewrite fill_app. Qed.


(* FIXME maybe *)
Inductive prim_step {S} : ∀ (e1 : expr S) (σ1 : state)
          (e2 : expr S) (σ2 : state) (n : nat * nat), Prop :=
| Ectx_step e1 σ1 e2 σ2 n (K1 K2 : ectx S) e1' e2' :
  e1 = fill K1 e1' → e2 = fill K2 e2' →
  head_step e1' σ1 K1 e2' σ2 K2 n → prim_step e1 σ1 e2 σ2 n.
(* | App_cont_step e1 σ e2 (K : ectx S) v K' : *)
(*   e1 = (fill K (App (Val $ ContV K') (Val v))) -> *)
(*   e2 = (fill K' (Val v)) -> *)
(*   prim_step e1 σ e2 σ (2, 0). *)
(* CHECK *)

Lemma prim_step_pure {S} (e1 e2 : expr S) σ1 σ2 n :
  prim_step e1 σ1 e2 σ2 (n,0) → σ1 = σ2.
Proof.
  inversion 1; simplify_eq/=.
  by inversion H2.
Qed.

Inductive prim_steps {S} : expr S → state → expr S → state → nat * nat → Prop :=
| prim_steps_zero e σ :
  prim_steps e σ e σ (0, 0)
| prim_steps_abit e1 σ1 e2 σ2 e3 σ3 n1 m1 n2 m2 :
  prim_step e1 σ1 e2 σ2 (n1, m1) →
  prim_steps e2 σ2 e3 σ3 (n2, m2) →
  prim_steps e1 σ1 e3 σ3 (plus n1 n2, plus m1 m2)
.

Lemma Ectx_step' {S} (K1 K2 : ectx S) e1 σ1 e2 σ2 efs :
  head_step e1 σ1 K1 e2 σ2 K2 efs → prim_step (fill K1 e1) σ1 (fill K2 e2) σ2 efs.
Proof. econstructor; eauto. Qed.

Lemma prim_steps_app {S} nm1 nm2 (e1 e2 e3 : expr S) σ1 σ2 σ3 :
  prim_steps e1 σ1 e2 σ2 nm1 → prim_steps e2 σ2 e3 σ3 nm2 →
  prim_steps e1 σ1 e3 σ3 (plus nm1.1 nm2.1, plus nm1.2 nm2.2).
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

Lemma prim_step_steps_steps {S} (e1 e2 e3 : expr S) σ1 σ2 σ3 nm1 nm2 nm3 :
  nm3 = (plus nm1.1 nm2.1, plus nm1.2 nm2.2) ->
  prim_step e1 σ1 e2 σ2 nm1 → prim_steps e2 σ2 e3 σ3 nm2 -> prim_steps e1 σ1 e3 σ3 nm3.
Proof.
  intros -> H G.
  eapply prim_steps_app; last apply G.
  apply prim_step_steps, H.
Qed.

Lemma head_step_prim_step {S} (e1 e2 : expr S) σ1 σ2 nm :
  head_step e1 σ1 [] e2 σ2 [] nm -> prim_step e1 σ1 e2 σ2 nm.
Proof.
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
| typed_Input :
  typed Γ Input Tnat
| typed_Output e :
  typed Γ e Tnat →
  typed Γ (Output e) Tnat
(* | typed_Throw e1 e2 τ τ' : *)
(*   typed Γ e1 τ -> *)
(*   typed Γ e2 (Tcont τ) -> *)
(*   typed Γ (Throw e1 e2) τ' *)
| typed_Shift e τ :
  typed (Γ ▹ Tcont τ) e τ ->
  typed Γ (Shift e) τ
| typed_App_Cont (τ τ' : ty) e1 e2 :
  typed Γ e1 (Tcont τ) ->
  typed Γ e2 τ ->
  typed Γ (App e1 e2) τ'
| type_Reset e τ :
  typed Γ e τ ->
  typed Γ (Reset e) τ
(* CHECK *)
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

Global Instance OpNotationLK {S : Set} : OpNotation (ectx S) (nat_op) (val S) (ectx S) := {
  __op K op v := K ++ [NatOpLK op v]
  }.

Global Instance OpNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : OpNotation (F S) (nat_op) (ectx S) (ectx S) := {
  __op e op K := K ++ [NatOpRK op (__asSynExpr e)]
  }.

Class IfNotation (A B C D : Type) := { __if : A -> B -> C -> D }.

Global Instance IfNotationExpr {S : Set} {F G H : Set -> Type} `{AsSynExpr F, AsSynExpr G, AsSynExpr H} : IfNotation (F S) (G S) (H S) (expr S) := {
  __if e₁ e₂ e₃ := If (__asSynExpr e₁) (__asSynExpr e₂) (__asSynExpr e₃)
  }.

Global Instance IfNotationCondK {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} :
  IfNotation (ectx S) (F S) (G S) (ectx S) := {
  __if K e₂ e₃ := K ++ [IfCondK (__asSynExpr e₂) (__asSynExpr e₃)]
  }.

Global Instance IfNotationTrueK {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} :
  IfNotation (F S) (ectx S) (G S) (ectx S) := {
  __if b K e₃ := K ++ [IfCondK (__asSynExpr b) (__asSynExpr e₃)]
  }.

Global Instance IfNotationFalseK {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} :
  IfNotation (F S) (G S) (ectx S) (ectx S) := {
  __if b e2 K := K ++ [IfCondK (__asSynExpr b) (__asSynExpr e2)]
  }.

Class OutputNotation (A B : Type) := { __output : A -> B }.

Global Instance OutputNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} : OutputNotation (F S) (expr S) := {
  __output e := Output (__asSynExpr e)
  }.

Global Instance OutputNotationK {S : Set} : OutputNotation (ectx S) (ectx S) := {
  __output K := K ++ [OutputK]
  }.

Class ResetNotation (A B : Type) := { __reset : A -> B }.

Global Instance ResetNotationExpr {S : Set} {F : Set -> Type} `{AsSynExpr F} :
  ResetNotation (F S) (expr S) := { __reset e := Reset (__asSynExpr e) }.

Global Instance ResetNotationK {S : Set} : ResetNotation (ectx S) (ectx S) :=
  { __reset K := K ++ [ResetK] }.

(* Class ThrowNotation (A B C : Type) := { __throw : A -> B -> C }. *)

(* Global Instance ThrowNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : ThrowNotation (F S) (G S) (expr S) := { *)
(*   __throw e₁ e₂ := Throw (__asSynExpr e₁) (__asSynExpr e₂) *)
(*   }. *)

(* Global Instance ThrowNotationLK {S : Set} {F : Set -> Type} `{AsSynExpr F} : ThrowNotation (ectx S) (F S) (ectx S) := { *)
(*   __throw K e₂ := ThrowLK K (__asSynExpr e₂) *)
(*   }. *)

(* Global Instance ThrowNotationRK {S : Set} : ThrowNotation (val S) (ectx S) (ectx S) := { *)
(*   __throw v K := ThrowRK v K *)
(*   }. *)

Class AppNotation (A B C : Type) := { __app : A -> B -> C }.

Global Instance AppNotationExpr {S : Set} {F G : Set -> Type} `{AsSynExpr F, AsSynExpr G} : AppNotation (F S) (G S) (expr S) := {
  __app e₁ e₂ := App (__asSynExpr e₁) (__asSynExpr e₂)
  }.

Global Instance AppNotationLK {S : Set} : AppNotation (ectx S) (expr S) (ectx S) := {
  __app K e := K ++ [AppLK e]
  }.

Global Instance AppNotationRK {S : Set} {F : Set -> Type} `{AsSynExpr F} : AppNotation (F S) (ectx S) (ectx S) := {
  __app e K := K ++ [AppRK (__asSynExpr e)]
  }.

Notation of_val := Val (only parsing).

Notation "x '⋆' y" := (__app x%syn y%syn) (at level 40, y at next level, left associativity) : syn_scope.
Notation "x '+' y" := (__op x%syn Add y%syn) : syn_scope.
Notation "x '-' y" := (__op x%syn Sub y%syn) : syn_scope.
Notation "x '*' y" := (__op x%syn Mult y%syn) : syn_scope.
Notation "'if' x 'then' y 'else' z" := (__if x%syn y%syn z%syn) : syn_scope.
Notation "'output' x" := (__output x%syn) (at level 60) : syn_scope.
(* Notation "'throw' e₁ e₂" := (__throw e₁%syn e₂%syn) (at level 60) : syn_scope. *)
Notation "'#' n" := (LitV n) (at level 60) : syn_scope.
Notation "'input'" := (Input) : syn_scope.
Notation "'rec' e" := (RecV e%syn) (at level 60) : syn_scope.
Notation "'shift/cc' e" := (Shift e%syn) (at level 60) : syn_scope.
Notation "'reset' e" := (Reset e%syn) (at level 60) : syn_scope.
(* Notation "'cont' K" := (ContV K%syn) (at level 60) : syn_scope. *)
Notation "'$' fn" := (set_pure_resolver fn) (at level 60) : syn_scope.
(* Notation "□" := (EmptyK) : syn_scope. *)
Notation "K '⟪' e '⟫'" := (fill K%syn e%syn) (at level 60) : syn_scope.


Notation "'lam' e" := (LamV e%syn) (at level 60) : syn_scope.

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
  Example test21 : val ∅ := (lam (if ($ 0) then # 1 else #0)).
  Example test3 : expr ∅ := (shift/cc ($ 0)).
  Example test4 : expr ∅ := ((# 1) + (# 0)).
  Example test5 : val ∅ := (rec (if ($ 1) then # 1 else (($ 0) ⋆ (($ 1) - (# 1))))).
  Example test6 : expr (inc (inc ∅)) := ($ 0) ⋆ ($ 1).
  Example test7 : expr ∅ := (let_ ((rec (if ($ 1) then # 1 else (($ 0) ⋆ (($ 1) - (# 1))))) ⋆ (# 5)) in (output ($ 0))).

  Open Scope typing_scope.

  Example test8 : Prop := (empty_env ⊢ (# 0) : ℕ).
End SynExamples.

Definition compute_head_step {S}
  (e : expr S) (σ : state) (K : ectx S) :
  option (expr S * state * ectx S * (nat * nat)) :=
  match e with
  | (App (Val (RecV e1)) (Val v2)) =>
      Some ((subst (Inc := inc) ((subst (F := expr) (Inc := inc) e1)
                                   (Val (shift (Inc := inc) v2)))
               (Val (RecV e1))), σ, K, (1,0))
  | Input =>
      let '(n, σ') := update_input σ in
      Some ((Val (LitV n)), σ', K, (1, 1))
  | Output (Val (LitV n)) =>
      let σ' := update_output n σ in
      Some ((Val (LitV 0)), σ', K, (1, 1))
  | (NatOp op (Val v1) (Val v2)) =>
      let res := nat_op_interp op v1 v2 in
      option_rect (fun _ => option _) (fun v3 => Some ((Val v3), σ, K, (0, 0))) None res
  | (If (Val (LitV n)) e1 e2) =>
      if (decide (0 < n))
      then Some (e1, σ, K, (0, 0))
      else
        if (decide (n = 0))
        then Some (e2, σ, K, (0, 0))
        else None
  | (Shift e) =>
      let (Ki, Ko) := shift_context K in
      let f := cont_to_rec Ki in
      Some ((subst (Inc := inc) e (Val f)), σ, Ko, (1, 1))
  | (Reset (Val v)) => Some (Val v, σ, K, (1, 1))
  (* | (Reset (fill E (Shift e))) => None *)
  | _ => None
  end.
(* CHECK *)

Lemma head_step_reflect {S : Set} (e : expr S) (σ : state) (K : ectx S)
  : option_reflect (fun '(e', σ', K', nm) => head_step e σ K e' σ' K' nm)
      True
      (compute_head_step e σ K).
Proof.
  destruct e; try (by constructor).
  - destruct e1; try (by constructor).
    destruct v; try (by constructor).
    destruct e2; try (by constructor).
    constructor.
    constructor.
  - destruct e1; try (by constructor).
    destruct e2; try (by constructor).
    destruct (nat_op_interp op v v0) eqn:Heqn.
    + simpl; rewrite Heqn.
      simpl.
      constructor.
      by constructor.
    + simpl; rewrite Heqn.
      simpl.
      constructor.
      constructor.
  - destruct e1; try (by constructor).
    destruct v; try (by constructor).
    simpl.
    case_match; simpl.
    + constructor.
      constructor.
      assumption.
    + case_match; simpl.
      * constructor.
        constructor.
        assumption.
      * constructor.
        constructor.
  - simpl.
    destruct (update_input σ) eqn:Heqn.
    by do 2 constructor.
  - simpl.
    destruct e; try (by constructor).
    destruct v; try (by constructor).
    destruct (update_output n σ) eqn:Heqn.
    by do 2 constructor.
  - simpl. 
    destruct (shift_context K) as [Ki Ko] eqn:HK.
    constructor. apply ShiftS with Ki =>//=.
  -  simpl.
     destruct e; try (by constructor).
     do 2 constructor.
Qed.
