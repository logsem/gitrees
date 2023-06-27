(** Affine functions *)
From Equations Require Import Equations.
From iris.base_logic.lib Require Import na_invariants.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang Require Import lang interp.
From gitrees.examples Require Import store pairs.

Definition s : stuckness := λ e, e = OtherError.

Module io_lang.
  Definition state := input_lang.lang.state.
  Definition ty := input_lang.lang.ty.
  Definition expr := input_lang.lang.expr.
  Definition tyctx := tyctx ty.
  Definition typed {S} := input_lang.lang.typed (S:=S).
  Definition interp_closed {sz} (rs : gReifiers sz) `{!subReifier reify_io rs} (e : expr []) := input_lang.interp.interp_expr rs e ().

Section io_lang.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n, αv ≡ NatV n)%I.
  Solve All Obligations with solve_proper.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) := λne αv,
    (□ ∀ σ βv, has_substate σ -∗
               Φ1 βv -∗
               WP@{rs} IT_of_V αv ⊙ (IT_of_V βv) @ s {{ v, ∃ σ', Φ2 v ∗ has_substate σ' }})%I.
  Solve All Obligations with solve_proper.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tnat => interp_tnat
    | Tarr τ1 τ2 => interp_tarr (interp_ty τ1) (interp_ty τ2)
    end.

  (* Definition valid1 (α : IT) (τ : ty) : iProp := *)
  (*   (∀ σ, has_substate σ -∗ *)
  (*         WP@{rs} α @ s {{ v, ∃ σ', interp_ty τ v ∗ has_substate σ' }}). *)
  (* Lemma fundmanetal_closed (e : expr []) (τ : ty) : *)
  (*   typed empC e τ → *)
  (*   ⊢ valid1 (interp_closed rs e) τ. *)
  (* Proof. Admitted. *)
  Definition ssubst_valid {S} (Γ : tyctx S) (ss : ssubst S) : iProp :=
    ([∗ list] τx ∈ zip (list_of_tyctx Γ) (list_of_ssubst (E:=F) ss),
      interp_ty (τx.1) (τx.2))%I.

  #[global] Instance io_lang_interp_ty_pers  τ βv : Persistent (io_lang.interp_ty τ βv).
  Proof. induction τ; apply _. Qed.
  #[global] Instance ssubst_valid_pers {S} (Γ : tyctx S) ss : Persistent (ssubst_valid  Γ  ss).
  Proof. apply _. Qed.

  Definition valid1 {S}  (Γ : tyctx S) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    (∀ σ ss, has_substate σ -∗ ssubst_valid Γ ss -∗
          WP@{rs} α (interp_ssubst ss) @ s {{ v, ∃ σ', interp_ty τ v ∗ has_substate σ' }}).

  Lemma compat_nat {S} n (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_nat rs n) Tnat.
  Proof.
    iIntros (σ αs) "Hs Has".
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.
  Lemma compat_var {S} Ω τ (v : var S) :
    typed_var Ω v τ →
    ⊢ valid1 Ω (interp_var v) τ.
  Proof.
    intros Hv.
    iIntros (σ ss) "Hs Has".
    unfold ssubst_valid.
    iInduction Hv as [|? ? ? Ω v] "IH" forall (ss); simpl.
    - dependent elimination ss as [cons_ssubst αv ss].
      simp list_of_tyctx list_of_ssubst interp_ssubst.
      simp interp_var. simpl.
      iDestruct "Has" as "[H _]".
      iApply wp_val; eauto with iFrame.
    - dependent elimination ss as [cons_ssubst αv ss].
      simp list_of_tyctx list_of_ssubst interp_ssubst.
      simp interp_var. simpl.
      iDestruct "Has" as "[_ H]".
      by iApply ("IH" with "Hs H").
  Qed.
  Lemma compat_if {S} (Γ : tyctx S) τ α β1 β2 :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β1 τ -∗
      valid1 Γ β2 τ -∗
      valid1 Γ (interp_if rs α β1 β2) τ.
  Proof.
    iIntros "H0 H1 H2".
    iIntros (σ ss) "Hs #Has".
    iSpecialize ("H0" with "Hs Has").
    simpl. iApply (wp_bind _ (IFSCtx _ _)).
    { solve_proper. }
    iApply (wp_wand with "H0").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Hn".
    iModIntro. unfold IFSCtx.
    iRewrite "Hn".
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply ("H2" with "Hs Has").
    - rewrite IF_True; last lia.
      iApply ("H1" with "Hs Has").
  Qed.
  Lemma compat_input {S} (Γ : tyctx S) :
    ⊢ valid1 Γ (interp_input rs) Tnat.
  Proof.
    iIntros (σ ss) "Hs #Has".
    simpl.
    destruct (update_input σ) as [n σ'] eqn:Hinp.
    iApply (wp_input with "Hs") .
    { eauto. }
    iNext. iIntros "_ Hs".
    iApply wp_val. eauto with iFrame.
  Qed.
  Lemma compat_output {S} (Γ : tyctx S) α :
    ⊢ valid1 Γ α Tnat → valid1 Γ (interp_output rs α) Tnat.
  Proof.
    iIntros "H". iIntros (σ ss) "Hs #Has".
    simpl.
    iApply (wp_bind _ (get_nat _)).
    { solve_proper. }
    iSpecialize ("H" with "Hs Has").
    iApply (wp_wand with "H").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Hn".
    iModIntro. iRewrite "Hn".
    rewrite get_nat_nat.
    iApply (wp_output with "Hs").
    { reflexivity. }
    iNext. iIntros "_ Hs".
    eauto with iFrame.
  Qed.
  Lemma compat_app {S} (Γ : tyctx S) α β τ1 τ2 :
    ⊢ valid1 Γ α (Tarr τ1 τ2) -∗
      valid1 Γ β τ1 -∗
      valid1 Γ (interp_app rs α β) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (σ ss) "Hs #Has". simpl.
    iApply (wp_bind _  (AppRSCtx _)).
    { solve_proper. }
    iSpecialize ("H2" with "Hs Has").
    iApply (wp_wand with "H2").
    iIntros (βv) "Hb".
    iDestruct "Hb" as (σ') "[Hb Hs]".
    iModIntro. unfold AppRSCtx.
    iApply (wp_bind _ (AppLSCtx (IT_of_V βv))).
    { solve_proper. }
    iSpecialize ("H1" with "Hs Has").
    iApply (wp_wand with "H1").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ'') "[Ha  Hs]".
    iModIntro. unfold AppLSCtx.
    iApply ("Ha" with "Hs Hb").
  Qed.

  Lemma compat_rec {S} (Γ : tyctx S) τ1 τ2 α :
    ⊢ □ valid1 (consC (Tarr τ1 τ2) (consC τ1 Γ)) α τ2 -∗
      valid1 Γ (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (σ ss) "Hs #Hss".
    pose (env := (interp_ssubst ss)). fold env.
    simp subst_expr.
    pose (f := (ir_unf rs α env)).
    iAssert (interp_rec rs α env ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf".
    iApply wp_val. iModIntro. iExists _. iFrame.
    iLöb as "IH". iSimpl. iModIntro.
    clear σ.
    iIntros (σ βv) "Hs #Hw".
    iApply wp_lam.
    iNext.
    pose (ss' := cons_ssubst (FunV (Next f)) (cons_ssubst βv ss)).
    iSpecialize ("H" $! _ ss' with "Hs []").
    { unfold ssubst_valid.
      unfold ss'.
      simp list_of_tyctx list_of_ssubst.
      by iFrame "Hw IH Hss". }
    unfold f. simpl.
    unfold ss'. simp interp_ssubst.
    iAssert (IT_of_V (FunV (Next f)) ≡ interp_rec rs α env)%I as "Heq".
    { rewrite interp_rec_unfold. done. }
    iRewrite -"Heq". iApply "H".
  Qed.
  Lemma fundamental {S} (Γ : tyctx S) e τ :
    typed Γ e τ → ⊢ valid1 Γ (interp_expr rs e) τ
  with fundamental_val {S} (Γ : tyctx S) v τ :
    typed_val Γ v τ → ⊢ valid1 Γ (interp_val rs v) τ.
  Proof.
    - destruct 1.
      + by iApply fundamental_val.
      + by iApply compat_var.
      + iApply compat_rec; iApply fundamental; eauto.
      + iApply compat_app; iApply fundamental; eauto.
      + admit.
      + iApply compat_if;  iApply fundamental; eauto.
      + iApply compat_input.
      + iApply compat_output; iApply fundamental; eauto.
    - destruct 1.
      + iApply compat_nat.
      + iApply compat_rec; iApply fundamental; eauto.
  Admitted.
  Lemma fundmanetal_closed (e : expr []) (τ : ty) :
    typed empC e τ →
    ⊢ valid1 empC (interp_expr rs e) τ.
  Proof. apply fundamental. Qed.

End io_lang.
End io_lang.

#[global] Instance io_lang_interp_ty_pers {sz} (rs : gReifiers sz) `{!subReifier reify_io rs} `{!invGS Σ, !stateG rs Σ} τ βv : Persistent (io_lang.interp_ty rs τ βv).
Proof. induction τ; apply _. Qed.



Inductive ty :=
  tBool | tInt | tUnit
| tArr (τ1 τ2 : ty) | tPair (τ1 τ2 : ty).

Inductive expr : scope → Type :=
| LitBool (b : bool) {S} : expr S
| LitNat (n : nat) {S} : expr S
| LitUnit {S} : expr S
| Lam {S} : expr (tt::S) → expr S
| Var {S} : var S → expr S
| App {S1 S2} : expr S1 → expr S2 → expr (S1++S2)
(* | EPair {S} : expr S → expr S → expr S *)
(* | EDestruct {S} : expr S → expr (()::()::S) → expr S *)
| EEmbed {S} : io_lang.expr [] → expr S
.

Local Notation tyctx := (tyctx ty).
Inductive typed : forall {S}, tyctx  S → expr S → ty → Prop :=
| typed_Var {S} (Ω : tyctx S) (τ : ty) (v : var S)  :
  typed_var Ω v τ →
  typed Ω (Var v) τ
| typed_Lam {S} (Ω : tyctx S) (τ1 τ2 : ty) (e : expr (()::S) ) :
  typed (consC τ1 Ω) e τ2 →
  typed Ω (Lam e) (tArr τ1 τ2)
| typed_App {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tArr τ1 τ2) →
  typed Ω2 e2 τ1 →
  typed (tyctx_app Ω1 Ω2) (App e1 e2) τ2
| typed_Nat {S} (Ω : tyctx S) n :
  typed Ω (LitNat n) tInt
| typed_Bool {S} (Ω : tyctx S) b :
  typed Ω (LitBool b) tBool
| typed_Unit {S} (Ω : tyctx S) :
  typed Ω LitUnit tUnit
.

Inductive ty_conv : ty → input_lang.lang.ty → Type :=
| ty_conv_bool : ty_conv tBool Tnat
| ty_conv_int  : ty_conv tInt  Tnat
| ty_conv_unit : ty_conv tUnit Tnat
| ty_conv_fun {τ1 τ2 t1 t2} :
  ty_conv τ1 t1 → ty_conv τ2 t2 →
  ty_conv (tArr τ1 τ2) (Tarr (Tarr Tnat t1) t2)
.


Section affine.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS Σ, !stateG rs Σ, !heapG rs Σ}.
  Notation iProp := (iProp Σ).

  Program Definition thunked : IT -n> locO -n> IT := λne e ℓ,
      λit _, IF (READ ℓ) (Err OtherError)
                         (SEQ (WRITE ℓ (Nat 1)) e).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  Program Definition thunkedV : IT -n> locO -n> ITV := λne e ℓ,
      FunV $ Next (λne _, IF (READ ℓ) (Err OtherError) (SEQ (WRITE ℓ (Nat 1)) e)).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  #[export] Instance tv_into_val e l : IntoVal (thunked e l) (thunkedV e l).
  Proof.
    unfold IntoVal. simpl. f_equiv. f_equiv. intro.
    done.
  Qed.
  Program Definition Thunk : IT -n> IT := λne e,
      ALLOC (Nat 0) (thunked e).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  Program Definition Force : IT -n> IT := λne e, e ⊙ (Nat 0).

  Local Open Scope type.
  Definition interp_litbool (b : bool) {A} : A -n> IT := λne _,
    Nat (if b then 1 else 0).
  Definition interp_litnat (n : nat) {A} : A -n> IT := λne _,
    Nat n.
  Definition interp_litunit {A} : A -n> IT := λne _, Nat 0.
  Program Definition interp_pair {A1 A2} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    pairT (t1 env.1) (t2 env.2).  (* we don't need to evaluate the pair here, i.e. lazy pairs? *)
  Next Obligation. solve_proper_please. Qed.
  Program Definition interp_lam {A : ofe} (b : (IT * A) -n> IT) : A -n> IT := λne env,
    λit x, b (x,env).
  Solve All Obligations with solve_proper_please.
  Program Definition interp_app {A1 A2 : ofe} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    LET (t2 env.2) $ λne x,
    LET (t1 env.1) $ λne f,
    APP' f (Thunk x).
  Solve All Obligations with solve_proper_please.
  (* Program Definition interp_destruct {A1 A2 : ofe} *)
  (*      (ps : A1 -n> IT) (t : IT*IT*A2 -n> IT) *)
  (*   : A1*A2 -n> IT := λne env, *)
  (*   LET (ps env.1) $ λne ps, *)
  (*   LET (Thunk (proj1T ps)) $ λne x, *)
  (*   LET (Thunk (proj2T ps)) $ λne y, *)
  (*   t (x, y, env.2). *)
  (* Solve All Obligations with solve_proper_please. *)

  Definition interp_scope_split {S1 S2} {E} :
    interp_scope (E:=E) (S1 ++ S2) -n> interp_scope (E:=E) S1 * interp_scope (E:=E) S2.
  Proof.
    induction S1 as [|? S1]; simpl.
    - simple refine (λne x, (tt, x)).
      solve_proper.
    - simple refine (λne xy, let ss := IHS1 xy.2 in ((xy.1, ss.1), ss.2)).
      solve_proper.
  Defined.

  Fixpoint interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | LitBool b => interp_litbool b
    | LitNat n  => interp_litnat n
    | LitUnit   => interp_litunit
    | Var v     => Force ◎ interp_var v
    | Lam e    => interp_lam (interp_expr e)
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EEmbed io_expr => constO (io_lang.interp_closed rs io_expr)
    end.


  Context `{A:ofe}.
  Variable (P : A → iProp).
  Context `{!NonExpansive P}.

  Program Definition expr_pred (α : IT) (Φ : ITV -n> iProp) : iProp :=
    (∀ x : A, P x -∗ WP@{rs} α @ s {{ v, ∃ y : A, Φ v ∗ P y }}).
  #[global] Instance expr_pred_ne : NonExpansive2 expr_pred.
  Proof. solve_proper. Qed.
  (* interpreting tys *)
  Program Definition protected (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (WP@{rs} Force (IT_of_V αv) @ s {{ Φ }})%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tbool : ITV -n> iProp := λne αv,
    (αv ≡ NatV 0 ∨ αv ≡ NatV 1)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n, αv ≡ NatV n)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tunit : ITV -n> iProp := λne αv,
    (αv ≡ NatV 0)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tpair (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ β1v β2v, IT_of_V αv ≡ pairTV (IT_of_V β1v) (IT_of_V β2v) ∗
                       Φ1 β1v ∗ Φ2 β2v)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∀ βv, Φ1 βv -∗ expr_pred ((IT_of_V αv) ⊙ (Thunk (IT_of_V βv))) Φ2)%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tBool => interp_tbool
    | tUnit => interp_tunit
    | tInt  => interp_tnat
    | tPair τ1 τ2 => interp_tpair (interp_ty τ1) (interp_ty τ2)
    | tArr τ1 τ2  => interp_tarr  (interp_ty τ1) (interp_ty τ2)
    end.

  Definition ssubst_valid {S} (Ω : tyctx S) (ss : ssubst S) : iProp :=
    ([∗ list] τx ∈ zip (list_of_tyctx Ω) (list_of_ssubst (E:=F) ss),
      protected (interp_ty (τx.1)) (τx.2))%I.

  Definition valid1 {S} (Ω : tyctx S) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    ∀ ss,  ssubst_valid Ω ss -∗ heap_ctx -∗ expr_pred (α (interp_ssubst ss)) (interp_ty τ).

  Lemma compat_bool {S} b (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_litbool b) tBool.
  Proof.
    iIntros (αs) "Has #Hctx".
    iIntros (x) "Hx".
    simpl. iApply wp_val. iModIntro.
    destruct b; simpl; eauto.
  Qed.
  Lemma compat_nat {S} n (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_litnat n) tInt.
  Proof.
    iIntros (αs) "Has #Hctx".
    iIntros (x) "Hx".
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.
  Lemma compat_unit {S} (Ω : tyctx S) :
    ⊢ valid1 Ω interp_litunit tUnit.
  Proof.
    iIntros (αs) "Has #Hctx".
    iIntros (x) "Hx".
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.

  (* Lemma compat_pair {A1 A2 : ofe} (e1 : A1) (e2 : A2) (Φ1 Φ2 : ITV -n> iProp) *)
  (*   (α : A1 -n> IT) (β : A2 -n> IT) s : *)
  (*   heap_ctx ⊢ WP@{rs} α e1 @ s {{ Φ1 }} -∗ *)
  (*              WP@{rs} β e2 @ s {{ Φ2 }} -∗ *)
  (*              WP@{rs} interp_pair α β (e1,e2) @ s {{ interp_tpair Φ1 Φ2 }}. *)
  (* Proof. *)
  (*   iIntros "#Hctx H1 H2". *)
  (*   Opaque pairTV. iSimpl. *)
  (*   iApply (wp_bind _ (get_val _)). *)
  (*   { solve_proper. } *)
  (*   iApply (wp_wand with "H2"). *)
  (*   iIntros (βv) "H2". iModIntro. *)
  (*   rewrite get_val_ITV. simpl. *)
  (*   iApply (wp_bind _ (get_val _)). *)
  (*   { solve_proper. } *)
  (*   iApply (wp_wand with "H1"). *)
  (*   iIntros (αv) "H1". iModIntro. *)
  (*   rewrite get_val_ITV. simpl. *)
  (*   iApply wp_val. *)
  (*   iModIntro. *)
  (*   iExists αv,βv. iSplit; eauto with iFrame. *)
  (* Qed. *)
  (* Lemma compat_destruct {A1 A2 : ofe} (e1 : A1) (e2 : A2) *)
  (*   (Φ1 Φ2 Φ : ITV -n> iProp) (α : IT*IT*A2 -n> IT) (β : A1 -n> IT) s : *)
  (*   heap_ctx ⊢ WP@{rs} β e1 @ s {{ interp_tpair Φ1 Φ2 }} -∗ *)
  (*              (∀ β1v β2v, protected Φ1 β1v -∗ protected Φ2 β2v -∗ *)
  (*                     WP@{rs} α (IT_of_V β1v,IT_of_V β2v,e2) @ s {{ Φ }}) -∗ *)
  (*              WP@{rs} (interp_destruct β α (e1,e2)) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   Local Opaque thunked thunkedV proj1T proj2T pairTV. *)
  (*   iIntros "#Hctx H1 H2". *)
  (*   iSimpl. *)
  (*   iApply wp_let. *)
  (*   iApply (wp_wand with "H1"). *)
  (*   iIntros (βv) "H1". iModIntro. *)
  (*   iApply wp_let. *)
  (*   iApply (wp_alloc with "Hctx"). *)
  (*   { solve_proper_please. } *)
  (*   iNext. iNext. iIntros (l1) "Hl1". *)
  (*   iApply (wp_val _ _ (thunkedV _ _)). *)
  (*   iModIntro. iSimpl. *)
  (*   iApply wp_let. *)
  (*   iApply (wp_alloc with "Hctx"). *)
  (*   { solve_proper_please. } *)
  (*   iNext. iNext. iIntros (l2) "Hl2". *)
  (*   iApply (wp_val _ _ (thunkedV _ _)). *)
  (*   iModIntro. iSimpl. *)
  (*   iSimpl in "H1". *)
  (*   iDestruct "H1" as (βv1 βv2) "(#Hb & Hb1 & Hb2)". *)
  (*   iRewrite "Hb". iClear "Hb". *)
  (*   Local Transparent thunkedV thunked. *)
  (*   iApply ("H2" with "[Hb1 Hl1] [Hb2 Hl2]"). *)
  (*   - simpl. iApply wp_lam. iNext. *)
  (*     simpl. *)
  (*     iApply (wp_bind _ (IFSCtx _ _)). *)
  (*     iApply (wp_read with "Hctx Hl1"). *)
  (*     iNext. iNext. iIntros "Hl1". *)
  (*     iApply wp_val. iModIntro. *)
  (*     unfold IFSCtx. simpl. *)
  (*     rewrite IF_False; last lia. *)
  (*     iApply wp_seq. *)
  (*     { solve_proper. } *)
  (*     iApply (wp_write with "Hctx Hl1"). *)
  (*     iNext. iNext. iIntros "Hl1". *)
  (*     rewrite proj1T_pairV. simpl. *)
  (*     repeat (iApply wp_tick; iNext). *)
  (*     by iApply wp_val. *)
  (*   - simpl. iApply wp_lam. iNext. *)
  (*     simpl. *)
  (*     iApply (wp_bind _ (IFSCtx _ _)). *)
  (*     iApply (wp_read with "Hctx Hl2"). *)
  (*     iNext. iNext. iIntros "Hl2". *)
  (*     iApply wp_val. iModIntro. *)
  (*     unfold IFSCtx. simpl. *)
  (*     rewrite IF_False; last lia. *)
  (*     iApply wp_seq. *)
  (*     { solve_proper. } *)
  (*     iApply (wp_write with "Hctx Hl2"). *)
  (*     iNext. iNext. iIntros "Hl2". *)
  (*     rewrite proj2T_pairV. simpl. *)
  (*     repeat (iApply wp_tick; iNext). *)
  (*     by iApply wp_val. *)
  (* Qed. *)

  Lemma compat_var {S} Ω τ (v : var S) :
    typed_var Ω v τ →
    ⊢ valid1 Ω (Force ◎ interp_var v) τ.
  Proof.
    iIntros (Hv ss) "Has #Hctx".
    iIntros (x) "Hx".
    unfold ssubst_valid.
    iInduction Hv as [|? ? ? Ω v] "IH" forall (ss); simpl.
    - dependent elimination ss as [cons_ssubst αv ss].
      simp list_of_tyctx list_of_ssubst interp_ssubst.
      simp interp_var. simpl.
      iDestruct "Has" as "[H _]".
      iApply (wp_wand with "H"); eauto with iFrame.
    - dependent elimination ss as [cons_ssubst αv ss].
      simp list_of_tyctx list_of_ssubst interp_ssubst.
      simp interp_var. simpl.
      iDestruct "Has" as "[_ H]".
      by iApply ("IH" with "H").
  Qed.

  Equations ssubst_split {S1 S2} (αs : ssubst (E:=F) (S1++S2)) : ssubst (E:=F) S1 * ssubst (E:=F) S2 :=
    ssubst_split (S1:=[]) αs := (emp_ssubst,αs);
    ssubst_split (S1:=u::_) (cons_ssubst αv αs) := (cons_ssubst αv (ssubst_split αs).1, (ssubst_split αs).2).


  Lemma ssubst_valid_app {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) αs :
    ssubst_valid (tyctx_app Ω1 Ω2) αs ⊢ ssubst_valid Ω1 (ssubst_split αs).1
                                      ∗ ssubst_valid Ω2 (ssubst_split αs).2.
  Proof.
    iInduction Ω1 as [|τ Ω1] "IH" forall (Ω2); simp tyctx_app ssubst_split.
    - simpl. iIntros "$". unfold ssubst_valid.
      simp list_of_ssubst list_of_tyctx. done.
    - iIntros "H".
      rewrite {4 5}/ssubst_valid.
      simpl in αs.
      dependent elimination αs as [cons_ssubst αv αs].
      simp ssubst_split. simpl.
      simp list_of_ssubst list_of_tyctx.
      simpl. iDestruct "H" as "[$ H]".
      by iApply "IH".
  Qed.
  Lemma interp_scope_ssubst_split {S1 S2} (αs : ssubst (S1++S2)) :
    interp_scope_split (interp_ssubst αs) ≡
      (interp_ssubst (ssubst_split αs).1, interp_ssubst (ssubst_split αs).2).
  Proof.
    induction S1 as [|u S1]; simpl.
    - simp ssubst_split. simpl.
      simp interp_ssubst. done.
    - dependent elimination αs as [cons_ssubst αv αs].
      simp ssubst_split. simpl.
      simp interp_ssubst. repeat f_equiv; eauto; simpl.
       + rewrite IHS1//.
       + rewrite IHS1//.
  Qed.
  Lemma compat_app {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2)
    α β τ1 τ2 :
    ⊢ valid1 Ω1 α (tArr τ1 τ2) -∗
      valid1 Ω2 β τ1 -∗
      valid1 (tyctx_app Ω1 Ω2) (interp_app α β ◎ interp_scope_split) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (αs) "Has #Hctx".
    iIntros (x) "Hx".
    iEval(cbn-[interp_app]).
    rewrite ssubst_valid_app.
    rewrite interp_scope_ssubst_split.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Ha1 Hctx").
    iSpecialize ("H2"  with "Ha2 Hctx").
    Local Opaque Thunk.
    iSimpl.
    iApply wp_let.
    { solve_proper. }
    iSpecialize ("H2" with "Hx").
    iApply (wp_wand with "H2").
    iIntros (βv) "H2".
    iDestruct "H2" as (y) "[H2 Hy]".
    iModIntro. iSimpl.
    iApply wp_let.
    { solve_proper. }
    iSpecialize ("H1" with "Hy").
    iApply (wp_wand with "H1").
    iIntros (αv) "H1".
    iDestruct "H1" as (z) "[H1 Hz]".
    iModIntro. simpl.
    iSpecialize ("H1" with "H2 Hz").
    iApply (wp_wand with "H1"). eauto with iFrame.
  Qed.

  Lemma compat_lam {S} (Ω : tyctx S) τ1 τ2 α :
    ⊢ valid1 (consC τ1 Ω) α τ2 -∗
      valid1 Ω (interp_lam α) (tArr τ1 τ2).
  Proof.
    iIntros "H".
    iIntros (αs) "Has #Hctx".
    iIntros (x) "Hx".
    iApply wp_val.
    iModIntro. simpl.
    iExists _; iFrame.
    iIntros (βv) "Hb". clear x.
    iIntros (x) "Hx".
    iApply (wp_bind _ (AppRSCtx _)).
    { solve_proper. }
    Local Transparent Thunk.
    Local Opaque thunked thunkedV.
    iSimpl. iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    unfold AppRSCtx.
    iApply wp_lam. iNext.
    iEval(cbn-[thunked]).
    iSpecialize ("H" $! (cons_ssubst (thunkedV (IT_of_V βv) l) αs)
             with "[-Hx] Hctx Hx").
    { unfold ssubst_valid.
      simp list_of_ssubst list_of_tyctx. simpl.
      iFrame.
      Local Transparent thunked thunkedV.
      iApply wp_lam. iNext. simpl.
      iApply (wp_bind _ (IFSCtx _ _)).
      iApply (wp_read with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val. iModIntro.
      unfold IFSCtx. simpl.
      rewrite IF_False; last lia.
      iApply wp_seq.
      { solve_proper. }
      iApply (wp_write with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val. iModIntro.
      iApply "Hb". }
    simp interp_ssubst.
    iApply "H".
  Qed.

  Lemma fundamental_affine {S} (Ω : tyctx S) (e : expr S) τ :
    typed Ω e τ →
    ⊢ valid1 Ω (interp_expr e) τ.
  Proof.
    induction 1; simpl.
    - by iApply compat_var.
    - by iApply compat_lam.
    - by iApply compat_app.
    - by iApply compat_nat.
    - by iApply compat_bool.
    - by iApply compat_unit.
  Qed.

End affine.

Section glue.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS Σ, !stateG rs Σ, !heapG rs Σ}.
  Notation iProp := (iProp Σ).

  Arguments Force {_ _}.
  Arguments Thunk {_ _ _}.
  Arguments thunked {_ _ _}.
  Arguments thunkedV {_ _ _}.

  Definition valid2 {S} (Ω : tyctx S) (α : interp_scope (E:=F) S -n> IT) (τ : ty) : iProp := valid1 rs has_substate Ω α τ.

  Program Definition glue_to_affine_fun (glue_from_affine glue_to_affine : IT -n> IT) : IT -n> IT := λne α,
    LET α $ λne α,
    λit xthnk,
      LET (Force xthnk) $ λne x,
      LET (glue_from_affine x) $ λne x,
      LET (α ⊙ (Thunk x)) glue_to_affine.
  Solve All Obligations with solve_proper_please.

  Program Definition glue_from_affine_fun (glue_from_affine glue_to_affine : IT -n> IT) : IT -n> IT := λne α,
    LET α $ λne α,
    LET (Thunk α) $ λne α,
    λit xthnk,
      LET (Force α) $ λne α,
      LET (Force xthnk) $ λne x,
      LET (glue_to_affine x) $ λne x,
      LET (α ⊙ (Thunk x)) glue_from_affine.
  Solve All Obligations with solve_proper_please.

  Program Definition glue2_bool : IT -n> IT := λne α,
      IF α (Nat 1) (Nat 0).

  Fixpoint glue_to_affine {τ t} (conv : ty_conv τ t) : IT -n> IT :=
    match conv with
    | ty_conv_bool => glue2_bool
    | ty_conv_int  => idfun
    | ty_conv_unit => constO (Nat 0)
    | ty_conv_fun conv1 conv2 => glue_to_affine_fun (glue_from_affine conv1) (glue_to_affine conv2)
    end
  with glue_from_affine  {τ t} (conv : ty_conv τ t) : IT -n> IT :=
    match conv with
    | ty_conv_bool => idfun
    | ty_conv_int  => idfun
    | ty_conv_unit => idfun
    | ty_conv_fun conv1 conv2 => glue_from_affine_fun (glue_from_affine conv2) (glue_to_affine conv1)
    end.

(* Typeclasses Opaque thunkedV. *)
Local Opaque thunked thunkedV Thunk.
Lemma compat_glue_to_affine_bool {S} (Ω : tyctx S) α :
  io_lang.valid1 rs empC α Tnat ⊢
  valid2 Ω (constO (glue2_bool (α ()))) tBool.
Proof.
  simpl.
  iIntros "H". unfold io_lang.valid1.
  iIntros (ss) "Has #Hctx". simpl.
  iIntros (σ) "Hs".
  iSpecialize ("H" $! _ emp_ssubst with "Hs []").
  { unfold io_lang.ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  iApply (wp_bind _ (IFSCtx _ _)).
  { solve_proper. }
  iApply (wp_wand with "H").
  iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
  iDestruct "Ha" as (n) "Ha".
  iRewrite "Ha".
  unfold IFSCtx.
  iModIntro.
  destruct n as [|n]; simpl.
  * rewrite IF_False ; last lia.
    iApply wp_val; eauto with iFrame.
  * rewrite IF_True ; last lia.
    iApply wp_val; eauto with iFrame.
Qed.
Lemma compat_glue_to_affine_nat {S} (Ω : tyctx S) α :
  io_lang.valid1 rs empC α Tnat ⊢
  valid2 Ω (constO (α ())) tInt.
Proof.
  simpl.
  iIntros "H". unfold io_lang.valid1.
  iIntros (ss) "Has #Hctx". simpl.
  iIntros (σ) "Hs".
  iSpecialize ("H" $! _ emp_ssubst with "Hs []").
  { unfold io_lang.ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  iApply (wp_wand with "H").
  iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
  eauto with iFrame.
Qed.
Lemma compat_glue_from_affine_bool α :
  valid2 empC α tBool ⊢
  heap_ctx -∗ io_lang.valid1 rs empC α Tnat.
Proof.
  simpl.
  iIntros "H #Hctx". unfold io_lang.valid1.
  iIntros (σ ss) "Hs Hss".
  iSpecialize ("H" $! emp_ssubst with "[] Hctx Hs").
  { unfold ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  dependent elimination ss as [emp_ssubst].
  iApply (wp_wand with "H").
  iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
  iModIntro. iExists _; iFrame.
  iDestruct "Ha" as "[Ha|Ha]"; iExists _; eauto.
Qed.
Lemma compat_glue_from_affine_nat α :
  valid2 empC α tInt ⊢
  heap_ctx -∗ io_lang.valid1 rs empC α Tnat.
Proof.
  simpl.
  iIntros "H #Hctx". unfold io_lang.valid1.
  iIntros (σ ss) "Hs Hss".
  iSpecialize ("H" $! emp_ssubst with "[] Hctx Hs").
  { unfold ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  dependent elimination ss as [emp_ssubst].
  iApply (wp_wand with "H").
  iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
  iModIntro. iExists _; iFrame.
Qed.
Lemma compat_glue_from_affine_unit α :
  valid2 empC α tUnit ⊢
  heap_ctx -∗ io_lang.valid1 rs empC α Tnat.
Proof.
  simpl.
  iIntros "H #Hctx". unfold io_lang.valid1.
  iIntros (σ ss) "Hs Hss".
  iSpecialize ("H" $! emp_ssubst with "[] Hctx Hs").
  { unfold ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  dependent elimination ss as [emp_ssubst].
  iApply (wp_wand with "H").
  iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
  iModIntro. iExists _; iFrame.
  iExists 0. iApply "Ha".
Qed.

Lemma compat_glue_to_affine_fun {S} (Ω : tyctx S) (τ1 τ2 : ty)
  (τ1' τ2' : io_lang.ty) α (glue_to_affine glue_from_affine : IT -n> IT) :
  (∀ α, io_lang.valid1 rs empC α τ2'
        ⊢ valid2 Ω (constO (glue_to_affine (α ()))) τ2) →
  (∀ α,  valid2 empC (constO α) τ1
        ⊢ heap_ctx -∗  io_lang.valid1 rs empC
                               (constO (glue_from_affine α)) τ1') →
  io_lang.valid1 rs empC α (Tarr (Tarr Tnat τ1') τ2')
  ⊢ valid2 Ω
      (constO (glue_to_affine_fun glue_from_affine glue_to_affine (α ())))
      (tArr τ1 τ2).
Proof.
  intros G1 G2.
  iIntros "H".
  iIntros (αs) "Has #Hctx".
  iIntros (σ) "Hs".
  simpl. iApply wp_let.
  { solve_proper. }
  iSpecialize ("H" $! _ emp_ssubst with "Hs []").
  { unfold io_lang.ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  iApply (wp_wand with "H").
  iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
  iSimpl in "Ha". iDestruct "Ha" as "#Ha".
  iSimpl. iModIntro.
  iApply wp_val. iModIntro.
  simpl. iExists σ'. iFrame.
  iIntros (βv) "Hb".
  (* preparing a thunk *)
  iSimpl. clear σ.
  iIntros (σ) "Hs".
  iApply (wp_bind _ (AppRSCtx _)).
  { solve_proper. }
  iApply (wp_alloc with "Hctx").
  { solve_proper. }
  iNext. iNext. iIntros (l) "Hl".
  iApply wp_val. iModIntro.
  unfold AppRSCtx.
  iApply wp_lam. iNext.
  iEval(cbn-[thunked]).
  iApply wp_let.
  { solve_proper. }
  iApply wp_lam.
  (* forcing a thunk *)
  iNext. iSimpl.
  iApply (wp_bind _ (IFSCtx _ _)).
  { solve_proper. }
  iApply (wp_read with "Hctx Hl").
  iNext. iNext. iIntros "Hl".
  iApply wp_val. iModIntro.
  unfold IFSCtx. simpl.
  rewrite IF_False; last lia.
  iApply wp_seq.
  { solve_proper. }
  iApply (wp_write with "Hctx Hl").
  iNext. iNext. iIntros "Hl".
  iApply wp_val. iModIntro.
  (* doing the glue for the argument *)
  iApply (wp_let).
  { solve_proper. }
  iPoseProof (G2 (IT_of_V βv)) as "G2".
  iSpecialize ("G2" with "[Hb]").
  { iIntros (ss) "Hss _".
    iIntros (σ0) "Hs". simpl.
    iApply wp_val. eauto with iFrame. }
  iSpecialize ("G2" with "Hctx").
  iSpecialize ("G2" $! _ emp_ssubst with "Hs []").
  { unfold io_lang.ssubst_valid.
    simp list_of_tyctx list_of_ssubst.
    done. }
  iApply (wp_wand with "G2").
  iIntros (β'v) "Hb". iModIntro.
  simpl. clear σ σ'. iDestruct "Hb" as (σ) "[#Hb Hs]".
  (* calling the original function *)
  iApply wp_let.
  { solve_proper. }
  iApply (wp_bind _ (AppRSCtx _)).
  { solve_proper. }
  iApply (wp_alloc with "Hctx").
  { solve_proper. }
  iNext. iNext. iIntros (l') "Hl'".
  iApply (wp_val _ _ (thunkedV _ _)).
  iModIntro.
  unfold AppRSCtx.
  iClear "Hl". clear l.
  iApply fupd_wp.
  { solve_proper. }
  iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Nat n)) with "[Hl']") as "#Hinv".
  { iNext. iExists _; done. }
  iPoseProof ("Ha" $! _ (thunkedV (IT_of_V β'v) l') with "Hs [-Has]") as "H1".
  { iModIntro. iIntros (σ' βn) "Hs".
    iDestruct 1 as (m) "Hbm".
    iApply wp_lam. iNext. iSimpl.
    iApply (wp_bind _ (IFSCtx _ _)).
    { solve_proper. }
    iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
    { set_solver. }
    iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
    iModIntro. iExists (Nat n). iFrame.
    iNext. iNext. iIntros "Hl'".
    iMod ("Hcl" with "[Hl']") as "_".
    { iNext. eauto with iFrame. }
    iModIntro. iApply wp_val.
    iModIntro.
    unfold IFSCtx. simpl.
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply wp_seq.
      { solve_proper. }
      iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
      { set_solver. }
      iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
      iModIntro. iExists (Nat n). iFrame.
      iNext. iNext. iIntros "Hl'".
      iMod ("Hcl" with "[Hl']") as "_".
      { iNext. eauto with iFrame. }
      iModIntro. iApply wp_val.
      iModIntro. eauto with iFrame.
    - rewrite IF_True; last lia.
      iApply wp_err. done. }
  iModIntro.
  iApply (wp_wand with "H1").
  iIntros (γv) "H2".
  iModIntro. iDestruct "H2" as (σ') "[#H2 Hs]".
  iPoseProof (G1 (constO (IT_of_V γv))) as "G1".
  iSpecialize ("G1" with "[H2]").
  { iIntros (σ0 ss0) "Hs Has". simpl.
    iApply wp_val. iModIntro. eauto with iFrame. }
  iSpecialize ("G1" with "Has Hctx Hs").
  simpl. done.
Qed.

  Lemma glue_to_affine_compatibility {S} (Ω : tyctx S) (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') α :
    io_lang.valid1 rs empC α τ1' ⊢ valid2 Ω (constO (glue_to_affine Hconv (α ()))) τ1
  with glue_from_affine_compatibility (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') (α : IT) :
    valid2 empC (constO α) τ1 ⊢ heap_ctx -∗ io_lang.valid1 rs empC (constO (glue_from_affine Hconv α)) τ1'.
  Proof.
    - destruct Hconv.
      + by iApply compat_glue_to_affine_bool.
      + by iApply compat_glue_to_affine_nat.
      + iIntros "_".
        simpl. iApply compat_unit.
      + simpl. iApply compat_glue_to_affine_fun.
        * apply glue_to_affine_compatibility.
        * apply glue_from_affine_compatibility.
    - destruct Hconv.
      + iApply compat_glue_from_affine_bool.
      + iApply compat_glue_from_affine_nat.
      + iApply compat_glue_from_affine_unit.
      + Opaque io_lang.interp_tarr interp_tarr.
        iIntros "H #Hctx". iIntros (σ ss) "Hs _".
        simpl. clear ss.
        iSpecialize ("H" $! emp_ssubst with "[] Hctx Hs").
        { unfold ssubst_valid. simp list_of_tyctx list_of_ssubst.
          done. }
        simpl.
          simpl. iApply wp_let.
        { solve_proper. }
        iApply (wp_wand with "H").
        iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha Hs]".
        iSimpl in "Ha".
        iSimpl. iModIntro.
        iApply wp_let.
        { solve_proper. }
        iApply (wp_alloc with "Hctx").
        { solve_proper_please. }
        iNext. iNext. iIntros (l) "Hl".
        iApply (wp_val _ _ (thunkedV _ _)). iSimpl.
        iMod (inv_alloc (nroot.@"yolo") _
            (pointsto l (Nat 1) ∨ (pointsto l (Nat 0) ∗ (interp_tarr rs has_substate (interp_ty rs has_substate τ1) (interp_ty rs has_substate τ2) αv))) with "[Hl Ha]") as "#Hinv".
        { iNext. iRight. iFrame. }
        iModIntro. iApply wp_val.
        iModIntro. iExists _. iFrame.
        Transparent io_lang.interp_tarr. simpl.
        iModIntro. clear σ σ'. iIntros (σ βv) "Hs #Hb".
        iApply wp_lam. iNext.
        simpl.
        iApply wp_let.
        { solve_proper. }
        iSpecialize ("Hb" $! _ (NatV 0) with "Hs []").
        { eauto with iFrame. }
        iApply wp_lam.
        iNext. simpl.
       iApply (wp_bind _ (IFSCtx _ _)).
       { solve_proper_please. }
       iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
       { set_solver. }
       (** need thread local invariants *)
       iInv (nroot.@"yolo") as "[Hl | [Hl Ha]]" "Hcl".
       { iModIntro. iExists (Nat 1). iFrame.
         iNext. iNext. iIntros "Hl".
         iMod ("Hcl" with "[Hl]") as "_".
         { iNext. eauto with iFrame. }
         iModIntro. iApply wp_val.
         iModIntro.
         unfold IFSCtx. simpl.
         rewrite IF_True; last lia.
         iApply wp_err. done. }
       iModIntro. iExists (Nat 0). iFrame.
       iNext. iNext. iIntros "Hl".
       iMod ("Hcl" with "[Hl]") as "_".
       { iNext. eauto with iFrame. }
       iModIntro. iApply wp_val.
       iModIntro.
       unfold IFSCtx. simpl.
       rewrite IF_True; last lia.
         iApp;aly wp_err. done.
       destruct n as [|n].
       - rewrite IF_False; last lia.
         iApply wp_seq.
         { solve_proper. }
         iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
         { set_solver. }
         iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
         iModIntro. iExists (Nat n). iFrame.
         iNext. iNext. iIntros "Hl'".
         iMod ("Hcl" with "[Hl']") as "_".
         { iNext. eauto with iFrame. }
         iModIntro. iApply wp_val.
         iModIntro. eauto with iFrame.
       - rewrite IF_True; last lia.
         iApply wp_err. done. }

        iApply (wp_wand with "Hb"). clear βv.
        iIntros (βv). iDestruct 1 as (σ') "[#Hb Hs]".
        iModIntro. simpl.
        iApply wp_let.
        { solve_proper. }
        iPoseProof (glue_to_affine_compatibility _ empC _ _ Hconv1 (IT_of_V βv)) as "G1".
        iSpecialize ("G1" with "[Hb]").
        { iModIntro.
          iIntros (σ0) "Hs". simpl.
          iApply wp_val. iModIntro. eauto with iFrame. }
        iSpecialize ("G1" $! emp_ssubst with "[] Hctx Hs").
        { unfold ssubst_valid. simp list_of_tyctx list_of_ssubst.
          done. }
        simpl.
        iApply (wp_wand with "G1"). clear σ σ'.
        iIntros (γv). iDestruct 1 as (σ) "[Hg Hs]".
        iModIntro. iApply wp_let.
        { solve_proper. }
        iApply (wp_bind _ (AppRSCtx _)).
        { solve_proper. }
        iApply (wp_alloc with "Hctx").
        { solve_proper. }
        iNext. iNext. iIntros (l1) "Hl1".
        iApply wp_val. unfold AppRSCtx. iModIntro.
        iApply (wp_bind _ (AppLSCtx _)).
  Lemma compat_glue1_fun {S} (Ω : tyctx S) (τ1 τ2 : ty)
    (τ1' τ2' : io_lang.ty)
    (α : IT) (glue1 glue2 : IT -n> IT) (Φ1 Φ2 Φ1' Φ2' : ITV -n> iProp) :
    (heap_ctx ⊢ ∀ βv, interp_ty τ1 βv -∗ WP@{rs} glue1 (IT_of_V βv) @ s {{ x, □ Φ1' x }}) →
    (heap_ctx ⊢ ∀ βv, Φ2' βv -∗ WP@{rs} glue2 (IT_of_V βv) @ s {{ interp_ty τ2 }}) →
    (* α : (unit → τ1') → τ2' *)
    ⊢ io_lang.valid1 α (Tarr (Tarr Tnat τ1') τ2') →
    ⊢ valid1 Ω (constO (glue1_fun glue2 glue1 (IT_of_V αv))) (tArr τ1 τ2).
   Proof.
     intros G1 G2 Halpha.
     iIntros (αs) "Has #Hctx".
     iApply wp_val. iModIntro.
     Local Opaque thunked thunkedV.
     simpl.
     iIntros (βv) "Hb".
     (* preparing a thunk *)
     iSimpl. iApply (wp_bind _ (AppRSCtx _)).
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l) "Hl".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iApply wp_lam. iNext.
     iEval(cbn-[thunked]).
     iApply wp_let.
     { solve_proper. }
     iApply wp_lam.
     (* forcing a thunk *)
     iNext. iSimpl.
     iApply (wp_bind _ (IFSCtx _ _)).
     { solve_proper. }
     iApply (wp_read with "Hctx Hl").
     iNext. iNext. iIntros "Hl".
     iApply wp_val. iModIntro.
     unfold IFSCtx. simpl.
     rewrite IF_False; last lia.
     iApply wp_seq.
     { solve_proper. }
     iApply (wp_write with "Hctx Hl").
     iNext. iNext. iIntros "Hl".
     iApply wp_val. iModIntro.
     (* doing the glue for the argument *)
     iApply (wp_let).
     { solve_proper. }
     iPoseProof (G1 with "Hctx Hb") as "G1".
     iApply (wp_wand with "G1").
     iIntros (β'v) "#Hb". iModIntro.
     iSimpl.
     (* calling the original function *)
     iApply wp_let.
     { solve_proper. }
     iApply (wp_bind _ (AppRSCtx _)).
     { solve_proper. }
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l') "Hl'".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iClear "Hl". clear l.
     iApply fupd_wp.
     { solve_proper. }
     iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Nat n)) with "[Hl']") as "#Hinv".
     { iNext. iExists _; done. }
     iPoseProof (Halpha $! (thunkedV (IT_of_V β'v) l') with "[-]") as "H1".
     { iModIntro.
       iApply wp_lam. iNext. iSimpl.
       iApply (wp_bind _ (IFSCtx _ _)).
       iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
       { set_solver. }
       iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
       iModIntro. iExists (Nat n). iFrame.
       iNext. iNext. iIntros "Hl'".
       iMod ("Hcl" with "[Hl']") as "_".
       { iNext. eauto with iFrame. }
       iModIntro. iApply wp_val.
       iModIntro.
       unfold IFSCtx. simpl.
       destruct n as [|n].
       - rewrite IF_False; last lia.
         iApply wp_seq.
         { solve_proper. }
         iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
         { set_solver. }
         iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
         iModIntro. iExists (Nat n). iFrame.
         iNext. iNext. iIntros "Hl'".
         iMod ("Hcl" with "[Hl']") as "_".
         { iNext. eauto with iFrame. }
         iModIntro. iApply wp_val.
         iModIntro. done.
       - rewrite IF_True; last lia.
         iApply wp_err. done. }
     iModIntro.
     iApply (wp_wand with "H1").
     iIntros (γv) "H2".
     iModIntro.
     by iApply G2.
  Qed.

  Lemma compat_glue2_fun (αv : ITV) (glue1 glue2 : IT -n> IT) (Φ1 Φ2 Φ1' Φ2' : ITV -n> iProp) A :
    heap_ctx ⊢
      □ (∀ βv, Φ1' βv -∗ WP@{rs} glue1 (IT_of_V βv) @ s {{ Φ1 }}) -∗
      □ (∀ βv, Φ2 βv -∗ WP@{rs} glue2 (IT_of_V βv) @ s {{ x, □ Φ2' x }}) -∗
      □ (A -∗ interp_tarr Φ1 Φ2 αv) -∗
      (WP@{rs} glue1_fun glue2 glue1 (IT_of_V αv) @ s {{ αv,
            (* av : (unit →  τ1') → τ2' *)
            □ (∀ βv, □ (WP@{rs} IT_of_V βv ⊙ (Nat 0) @ s {{ Φ1' }}) -∗
                     WP@{rs} IT_of_V αv ⊙ (IT_of_V βv) @ s {{ Φ2' }}) }}).
   Proof.
     iIntros "#Hctx #G1 #G2 #H1 HA".
     iApply wp_val. iModIntro.
     iSpecialize ("H1" with "HA").
     iIntros (βv) "Hb".
     Local Opaque thunked thunkedV.
     iSimpl. iApply (wp_bind _ (AppRSCtx _)).
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l) "Hl".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iApply wp_lam. iNext.
     iEval(cbn-[thunked]).
     iApply wp_let.
     { solve_proper. }
     iApply wp_lam.
     (* forcing a thunk *)
     iNext. iSimpl.
     iApply (wp_bind _ (IFSCtx _ _)).
     { solve_proper. }
     iApply (wp_read with "Hctx Hl").
     iNext. iNext. iIntros "Hl".
     iApply wp_val. iModIntro.
     unfold IFSCtx. simpl.
     rewrite IF_False; last lia.
     iApply wp_seq.
     { solve_proper. }
     iApply (wp_write with "Hctx Hl").
     iNext. iNext. iIntros "Hl".
     iApply wp_val. iModIntro.
     (* doing the glue for the argument *)
     iApply (wp_let).
     { solve_proper. }
     iSpecialize ("G1" with "Hb").
     iApply (wp_wand with "G1").
     iIntros (β'v) "#Hb". iModIntro.
     iSimpl.
     (* calling the original function *)
     iApply wp_let.
     { solve_proper. }
     iApply (wp_bind _ (AppRSCtx _)).
     { solve_proper. }
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l') "Hl'".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iClear "Hl". clear l.
     iApply fupd_wp.
     { solve_proper. }
     iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Nat n)) with "[Hl']") as "#Hinv".
     { iNext. iExists _; done. }
     iSpecialize ("H1" $! (thunkedV (IT_of_V β'v) l') with "[-G2]").
     { iModIntro.
       iApply wp_lam. iNext. iSimpl.
       iApply (wp_bind _ (IFSCtx _ _)).
       iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
       { set_solver. }
       iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
       iModIntro. iExists (Nat n). iFrame.
       iNext. iNext. iIntros "Hl'".
       iMod ("Hcl" with "[Hl']") as "_".
       { iNext. eauto with iFrame. }
       iModIntro. iApply wp_val.
       iModIntro.
       unfold IFSCtx. simpl.
       destruct n as [|n].
       - rewrite IF_False; last lia.
         iApply wp_seq.
         { solve_proper. }
         iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
         { set_solver. }
         iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
         iModIntro. iExists (Nat n). iFrame.
         iNext. iNext. iIntros "Hl'".
         iMod ("Hcl" with "[Hl']") as "_".
         { iNext. eauto with iFrame. }
         iModIntro. iApply wp_val.
         iModIntro. done.
       - rewrite IF_True; last lia.
         iApply wp_err. done. }
     iModIntro.
     iApply (wp_wand with "H1").
     iIntros (γv) "H2".
     iModIntro.
     by iApply "G2".
   Qed.
