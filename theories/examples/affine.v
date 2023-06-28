(** Affine functions *)
From Equations Require Import Equations.
From iris.base_logic.lib Require Import na_invariants.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang Require Import lang interp logpred.
From gitrees.examples Require Import store pairs.


Module io_lang.
  Definition state := input_lang.lang.state.
  Definition ty := input_lang.lang.ty.
  Definition expr := input_lang.lang.expr.
  Definition tyctx := tyctx ty.
  Definition typed {S} := input_lang.lang.typed (S:=S).
  Definition interp_closed {sz} (rs : gReifiers sz) `{!subReifier reify_io rs} (e : expr []) := input_lang.interp.interp_expr rs e ().
End io_lang.


Inductive ty :=
  tBool | tInt | tUnit
| tArr (τ1 τ2 : ty) | tPair (τ1 τ2 : ty)
| tRef (τ : ty).

Local Notation tyctx := (tyctx ty).


Inductive expr : scope → Type :=
| LitBool (b : bool) {S} : expr S
| LitNat (n : nat) {S} : expr S
| LitUnit {S} : expr S
| Lam {S} : expr (tt::S) → expr S
| Var {S} : var S → expr S
| App {S1 S2} : expr S1 → expr S2 → expr (S1++S2)
| EPair {S1 S2} : expr S1 → expr S2 → expr (S1++S2)
| EDestruct {S1 S2} : expr S1 → expr (()::()::S2) → expr (S1++S2)
| Alloc {S} : expr S → expr S
| Replace {S1 S2} : expr S1 → expr S2 → expr (S1++S2)
| Dealloc {S} : expr S → expr S
| EEmbed {S} : io_lang.expr [] → expr S
.

Inductive typed : forall {S}, tyctx  S → expr S → ty → Prop :=
(** functions *)
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
(** pairs *)
| typed_Pair {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 τ1 →
  typed Ω2 e2 τ2 →
  typed (tyctx_app Ω1 Ω2) (EPair e1 e2) (tPair τ1 τ2)
| typed_Destruct {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 τ : ty)
  (e1 : expr S1) (e2 : expr (()::()::S2)) :
  typed Ω1 e1 (tPair τ1 τ2) →
  typed (consC τ1 (consC τ2 Ω2)) e2 τ →
  typed (tyctx_app Ω1 Ω2) (EDestruct e1 e2) τ
(** references *)
| typed_Alloc {S} (Ω : tyctx S) τ e :
  typed Ω e τ →
  typed Ω (Alloc e) (tRef τ)
| typed_Replace {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tRef τ1) →
  typed Ω2 e2 τ2 →
  typed (tyctx_app Ω1 Ω2) (Replace e1 e2) (tPair τ1 (tRef τ2))
| typed_Dealloc {S} (Ω : tyctx S) e τ :
  typed Ω e (tRef τ) →
  typed Ω (Dealloc e) tUnit
(** literals *)
| typed_Nat {S} (Ω : tyctx S) n :
  typed Ω (LitNat n) tInt
| typed_Bool {S} (Ω : tyctx S) b :
  typed Ω (LitBool b) tBool
| typed_Unit {S} (Ω : tyctx S) :
  typed Ω LitUnit tUnit
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

  Variable s : stuckness.
  Context `{A:ofe}.
  Variable (P : A → iProp).
  Context `{!NonExpansive P}.
  Local Notation expr_pred := (expr_pred s rs P).

  Program Definition thunked : IT -n> locO -n> IT := λne e ℓ,
      λit _, IF (READ ℓ) (Err OtherError)
                         (SEQ (WRITE ℓ (Nat 1)) e).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  Program Definition thunkedV : IT -n> locO -n> ITV := λne e ℓ,
      FunV $ Next (λne _, IF (READ ℓ) (Err OtherError) (SEQ (WRITE ℓ (Nat 1)) e)).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  #[export] Instance thunked_into_val e l : IntoVal (thunked e l) (thunkedV e l).
  Proof.
    unfold IntoVal. simpl. f_equiv. f_equiv. intro. done.
  Qed.

  Program Definition Thunk : IT -n> IT := λne e,
      ALLOC (Nat 0) (thunked e).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  Program Definition Force : IT -n> IT := λne e, e ⊙ (Nat 0).

  Local Open Scope type.

  Definition nat_of_loc (l : loc) := Pos.to_nat $ encode (loc_car l).
  Definition loc_of_nat (n : nat) :=
    match decode (Pos.of_nat n) with
    | Some l => Loc l
    | None   => Loc 0%Z
    end.

  Lemma loc_of_nat_of_loc l : loc_of_nat (nat_of_loc l) = l.
  Proof. Admitted.

  Definition interp_litbool (b : bool) {A} : A -n> IT := λne _,
    Nat (if b then 1 else 0).
  Definition interp_litnat (n : nat) {A} : A -n> IT := λne _,
    Nat n.
  Definition interp_litunit {A} : A -n> IT := λne _, Nat 0.
  Program Definition interp_pair {A1 A2} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    pairIT (t1 env.1) (t2 env.2).  (* we don't need to evaluate the pair here, i.e. lazy pairs? *)
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
  Program Definition interp_destruct {A1 A2 : ofe}
       (ps : A1 -n> IT) (t : IT*(IT*A2) -n> IT)
    : A1*A2 -n> IT := λne env,
    LET (ps env.1) $ λne ps,
    LET (Thunk (projIT1 ps)) $ λne x,
    LET (Thunk (projIT2 ps)) $ λne y,
    t (x, (y, env.2)).
  Solve All Obligations with solve_proper_please.
  Program Definition interp_alloc {A} (α : A -n> IT) : A -n> IT := λne env,
    LET (α env) $ λne α,
    ALLOC α $ λne l, Nat (nat_of_loc l).
  Solve All Obligations with solve_proper_please.
  Program Definition interp_replace {A1 A2} (α : A1 -n> IT) (β : A2 -n> IT) : A1*A2 -n> IT := λne env,
    LET (β env.2) $ λne β,
    flip get_nat (α env.1) $ λ n,
    LET (READ (loc_of_nat n)) $ λne γ,
    SEQ (WRITE (loc_of_nat n) β) (pairIT γ (Nat n)).
  Solve All Obligations with solve_proper_please.
  Program Definition interp_dealloc {A} (α : A -n> IT) : A -n> IT := λne env,
    flip get_nat (α env) $ λ n,
    DEALLOC (loc_of_nat n).
  Solve All Obligations with solve_proper_please.


  Fixpoint interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | LitBool b => interp_litbool b
    | LitNat n  => interp_litnat n
    | LitUnit   => interp_litunit
    | Var v     => Force ◎ interp_var v
    | Lam e    => interp_lam (interp_expr e)
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EPair e1 e2 => interp_pair (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EDestruct e1 e2 => interp_destruct (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | Alloc e => interp_alloc (interp_expr e)
    | Dealloc e => interp_dealloc (interp_expr e)
    | Replace e1 e2 => interp_replace (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EEmbed io_expr => constO (io_lang.interp_closed rs io_expr)
    end.

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
    (∃ β1v β2v, IT_of_V αv ≡ pairITV (IT_of_V β1v) (IT_of_V β2v) ∗
                       Φ1 β1v ∗ Φ2 β2v)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∀ βv, Φ1 βv -∗ expr_pred ((IT_of_V αv) ⊙ (Thunk (IT_of_V βv))) Φ2)%I.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_ref (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ (l : loc) βv, αv ≡ NatV (nat_of_loc l) ∗ pointsto l (IT_of_V βv) ∗ Φ βv)%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tBool => interp_tbool
    | tUnit => interp_tunit
    | tInt  => interp_tnat
    | tPair τ1 τ2 => interp_tpair (interp_ty τ1) (interp_ty τ2)
    | tArr τ1 τ2  => interp_tarr  (interp_ty τ1) (interp_ty τ2)
    | tRef τ   => interp_ref (interp_ty τ)
    end.

  Definition ssubst_valid {S} (Ω : tyctx S) ss :=
    lang_generic.ssubst_valid rs (λ τ, protected (interp_ty τ)) Ω ss.

  Definition valid1 {S} (Ω : tyctx S) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    ∀ ss, heap_ctx -∗ ssubst_valid Ω ss -∗ expr_pred (α (interp_ssubst ss)) (interp_ty τ).

  Lemma compat_pair {S1 S2} (Ω1: tyctx S1) (Ω2:tyctx S2) α β τ1 τ2 :
    ⊢ valid1 Ω1 α τ1 -∗
      valid1 Ω2 β τ2 -∗
      valid1 (tyctx_app Ω1 Ω2) (interp_pair α β ◎ interp_scope_split) (tPair τ1 τ2).
  Proof.
    Opaque pairITV.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_pair].
    unfold ssubst_valid.
    rewrite ssubst_valid_app.
    rewrite interp_scope_ssubst_split.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    iApply (expr_pred_bind with "H2").
    iIntros (βv) "Hb". simpl.
    rewrite -> get_val_ITV. simpl.
    iApply (expr_pred_bind with "H1").
    iIntros (αv) "Ha". simpl.
    rewrite -> get_val_ITV. simpl.
    iApply expr_pred_ret.
    iExists _,_. iFrame. done.
  Qed.

  Lemma wp_Thunk β  Φ `{!NonExpansive Φ}:
    ⊢ heap_ctx -∗
      ▷ (∀ l, pointsto l (Nat 0) -∗ Φ (thunkedV β l)) -∗
      WP@{rs} Thunk β @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx H".
    iSimpl. iApply (wp_alloc with "Hctx").
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    iApply ("H" with "Hl").
  Qed.
  Opaque Thunk.

  Lemma compat_destruct {S1 S2} (Ω1: tyctx S1) (Ω2:tyctx S2) α β τ1 τ2 τ :
    ⊢ valid1 Ω1 α (tPair τ1 τ2) -∗
      valid1 (consC τ1 $ consC τ2 Ω2) β τ -∗
      valid1 (tyctx_app Ω1 Ω2) (interp_destruct α β ◎ interp_scope_split) τ.
  Proof.
    Opaque pairITV thunked thunkedV projIT1 projIT2.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_destruct].
    unfold ssubst_valid.
    rewrite ssubst_valid_app.
    rewrite interp_scope_ssubst_split.
    iDestruct "Has" as "[Ha1 Ha2]".
    iSpecialize ("H1"  with "Hctx Ha1").
    simpl. iApply (expr_pred_bind (LETCTX _) with "H1").
    iIntros (αv) "Ha". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iDestruct "Ha" as (β1 β2) "[#Ha [Hb1 Hb2]]".
    iIntros (x) "Hx".
    iApply wp_let.
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    { solve_proper_please. }
    iNext. iIntros (l1) "Hl1". simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    { solve_proper_please. }
    iNext. iIntros (l2) "Hl2". simpl.
    iSpecialize ("H2" $! (cons_ssubst (thunkedV (projIT1 (IT_of_V αv)) l1)
                      $ cons_ssubst (thunkedV (projIT2 (IT_of_V αv)) l2) (ssubst_split αs).2)
                with "Hctx [-Hx] Hx").
    { unfold ssubst_valid. rewrite !ssubst_valid_cons.
      iFrame. Transparent thunkedV thunked.
      iSplitL "Hb1 Hl1".
      - simpl. iApply wp_lam. simpl. iNext.
        iApply (wp_bind _ (IFSCtx _ _)).
        iApply (wp_read with "Hctx Hl1").
        iNext. iNext. iIntros "Hl1".
        iApply wp_val. iModIntro. unfold IFSCtx.
        rewrite IF_False; last lia.
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write with "Hctx Hl1").
        iNext. iNext. iIntros "Hl1".
        iRewrite "Ha".
        rewrite projIT1_pairV. simpl.
        repeat iApply wp_tick.
        repeat iNext. iApply wp_val. done.
      - simpl. iApply wp_lam. simpl. iNext.
        iApply (wp_bind _ (IFSCtx _ _)).
        iApply (wp_read with "Hctx Hl2").
        iNext. iNext. iIntros "Hl2".
        iApply wp_val. iModIntro. unfold IFSCtx.
        rewrite IF_False; last lia.
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write with "Hctx Hl2").
        iNext. iNext. iIntros "Hl2".
        iRewrite "Ha".
        rewrite projIT2_pairV. simpl.
        repeat iApply wp_tick.
        repeat iNext. iApply wp_val. done.
    }
    simp interp_ssubst.
    iApply "H2".
  Qed.

  Lemma compat_alloc {S} (Ω : tyctx S) α τ:
    ⊢ valid1 Ω α τ -∗
      valid1 Ω (interp_alloc α) (tRef τ).
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iSpecialize ("H" with "Hctx Has").
    simpl. iApply (expr_pred_bind (LETCTX _) with "H").
    iIntros (αv) "Hav". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iApply expr_pred_frame.
    iApply (wp_alloc with "Hctx").
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro. simpl.
    eauto with iFrame.
  Qed.

  Lemma compat_replace {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) α β τ τ' :
    ⊢ valid1 Ω1 α (tRef τ) -∗
      valid1 Ω2 β τ' -∗
      valid1 (tyctx_app Ω1 Ω2) (interp_replace α β ◎ interp_scope_split) (tPair τ (tRef τ')).
  Proof.
    Opaque pairITV.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_replace].
    unfold ssubst_valid.
    rewrite ssubst_valid_app.
    rewrite interp_scope_ssubst_split.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    iApply (expr_pred_bind (LETCTX _) with "H2").
    iIntros (βv) "Hb". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iApply (expr_pred_bind with "H1").
    iIntros (αv) "Ha". simpl.
    iDestruct "Ha" as (l γ) "[Ha [Hl Hg]]".
    iApply expr_pred_frame.
    iRewrite "Ha". simpl.
    rewrite -> get_nat_nat.
    iApply wp_let.
    { solve_proper. }
    rewrite {1}loc_of_nat_of_loc.
    iApply (wp_read with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    simpl. iApply wp_seq.
    { solve_proper. }
    rewrite {1}loc_of_nat_of_loc.
    iApply (wp_write with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    rewrite get_val_ITV. simpl.
    rewrite get_val_ITV. simpl.
    iApply wp_val. iModIntro.
    iExists γ,(NatV (nat_of_loc l)).
    iSplit; first done.
    iFrame. eauto with iFrame.
  Qed.

  Lemma compat_dealloc {S} (Ω : tyctx S) α τ:
    ⊢ valid1 Ω α (tRef τ) -∗
      valid1 Ω (interp_dealloc α) tUnit.
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iSpecialize ("H" with "Hctx Has").
    iApply (expr_pred_bind with "H").
    iIntros (αv) "Ha /=".
    iDestruct "Ha" as (l βv) "[Ha [Hl Hb]]".
    iRewrite "Ha". iApply expr_pred_frame. simpl.
    rewrite -> get_nat_nat.
    rewrite loc_of_nat_of_loc.
    iApply (wp_dealloc with "Hctx Hl").
    iNext. iNext. eauto with iFrame.
  Qed.

  Lemma compat_bool {S} b (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_litbool b) tBool.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret.
    destruct b; simpl; eauto.
  Qed.
  Lemma compat_nat {S} n (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_litnat n) tInt.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret. eauto with iFrame.
  Qed.
  Lemma compat_unit {S} (Ω : tyctx S) :
    ⊢ valid1 Ω interp_litunit tUnit.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret. eauto with iFrame.
  Qed.
  Lemma compat_var {S} Ω τ (v : var S) :
    typed_var Ω v τ →
    ⊢ valid1 Ω (Force ◎ interp_var v) τ.
  Proof.
    iIntros (Hv ss) "#Hctx Has".
    iApply expr_pred_frame.
    unfold ssubst_valid.
    iInduction Hv as [|? ? ? Ω v] "IH" forall (ss); simpl.
    - dependent elimination ss as [cons_ssubst αv ss].
      rewrite ssubst_valid_cons.
      simp interp_var. simpl.
      iDestruct "Has" as "[H _]".
      simp interp_ssubst. simpl. done.
    - dependent elimination ss as [cons_ssubst αv ss].
      rewrite ssubst_valid_cons.
      simp interp_var. simpl.
      iDestruct "Has" as "[_ H]".
      simp interp_ssubst. simpl.
      by iApply ("IH" with "H").
  Qed.

  Lemma compat_app {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2)
    α β τ1 τ2 :
    ⊢ valid1 Ω1 α (tArr τ1 τ2) -∗
      valid1 Ω2 β τ1 -∗
      valid1 (tyctx_app Ω1 Ω2) (interp_app α β ◎ interp_scope_split) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    iEval(cbn-[interp_app]).
    unfold ssubst_valid.
    rewrite ssubst_valid_app.
    rewrite interp_scope_ssubst_split.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    Local Opaque Thunk.
    iSimpl.
    iApply (expr_pred_bind (LETCTX _) with "H2").
    iIntros (βv) "H2". unfold LETCTX. iSimpl.
    rewrite LET_Val/=.
    iApply (expr_pred_bind (LETCTX _) with "H1").
    iIntros (αv) "H1". unfold LETCTX. iSimpl.
    rewrite LET_Val/=.
    by iApply "H1".
  Qed.

  Lemma compat_lam {S} (Ω : tyctx S) τ1 τ2 α :
    ⊢ valid1 (consC τ1 Ω) α τ2 -∗
      valid1 Ω (interp_lam α) (tArr τ1 τ2).
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
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
             with "Hctx [-Hx] Hx").
    { unfold ssubst_valid.
      rewrite ssubst_valid_cons. iFrame.
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
    - by iApply compat_pair.
    - by iApply compat_destruct.
    - by iApply compat_alloc.
    - by iApply compat_replace.
    - by iApply compat_dealloc.
    - by iApply compat_nat.
    - by iApply compat_bool.
    - by iApply compat_unit.
  Qed.

  Lemma wp_app_thunk α β `{!AsVal β} Φ `{!NonExpansive Φ}:
    ⊢ heap_ctx -∗
      ▷ (∀ l, pointsto l (Nat 0) -∗ WP@{rs} α ⊙ (thunked β l) @ s {{ Φ }}) -∗
      WP@{rs} α ⊙ (Thunk β) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx H".
    iApply (wp_bind _ (AppRSCtx _)).
    iSimpl. iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    unfold AppRSCtx.
    rewrite thunked_into_val.
    iApply ("H" with "Hl").
  Qed.

End affine.

Arguments Force {_ _}.
Arguments Thunk {_ _ _}.
Arguments thunked {_ _ _}.
Arguments thunkedV {_ _ _}.

Arguments interp_tarr {_ _ _ _ _ _ _ _ _}.
Arguments interp_ty {_ _ _ _ _ _ _ _ _ _} _.
Local Arguments logpred.interp_tarr {_ _ _ _ _ _ _ _ _}.
Local Arguments logpred.interp_ty {_ _ _ _ _ _ _ _ _} _.

Inductive ty_conv : ty → io_lang.ty → Type :=
| ty_conv_bool : ty_conv tBool Tnat
| ty_conv_int  : ty_conv tInt  Tnat
| ty_conv_unit : ty_conv tUnit Tnat
| ty_conv_fun {τ1 τ2 t1 t2} :
  ty_conv τ1 t1 → ty_conv τ2 t2 →
  ty_conv (tArr τ1 τ2) (Tarr (Tarr Tnat t1) t2)
.

Inductive typed_glued : forall {S}, tyctx  S → expr S → ty → Type :=
(** FFI *)
| typed_Glue {S} (Ω : tyctx S) τ' τ e :
  ty_conv τ τ' →
  io_lang.typed empC e τ' →
  typed_glued Ω (EEmbed e) τ
(** functions *)
| typed_VarG {S} (Ω : tyctx S) (τ : ty) (v : var S)  :
  typed_var Ω v τ →
  typed_glued Ω (Var v) τ
| typed_LamG {S} (Ω : tyctx S) (τ1 τ2 : ty) (e : expr (()::S) ) :
  typed_glued (consC τ1 Ω) e τ2 →
  typed_glued Ω (Lam e) (tArr τ1 τ2)
| typed_AppG {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω1 e1 (tArr τ1 τ2) →
  typed_glued Ω2 e2 τ1 →
  typed_glued (tyctx_app Ω1 Ω2) (App e1 e2) τ2
(** pairs *)
| typed_PairG {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω1 e1 τ1 →
  typed_glued Ω2 e2 τ2 →
  typed_glued (tyctx_app Ω1 Ω2) (EPair e1 e2) (tPair τ1 τ2)
| typed_DestructG {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 τ : ty)
  (e1 : expr S1) (e2 : expr (()::()::S2)) :
  typed_glued Ω1 e1 (tPair τ1 τ2) →
  typed_glued (consC τ1 (consC τ2 Ω2)) e2 τ →
  typed_glued (tyctx_app Ω1 Ω2) (EDestruct e1 e2) τ
(** references *)
| typed_AllocG {S} (Ω : tyctx S) τ e :
  typed_glued Ω e τ →
  typed_glued Ω (Alloc e) (tRef τ)
| typed_ReplaceG {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω1 e1 (tRef τ1) →
  typed_glued Ω2 e2 τ2 →
  typed_glued (tyctx_app Ω1 Ω2) (Replace e1 e2) (tPair τ1 (tRef τ2))
| typed_DeallocG {S} (Ω : tyctx S) e τ :
  typed_glued Ω e (tRef τ) →
  typed_glued Ω (Dealloc e) tUnit
(** literals *)
| typed_NatG {S} (Ω : tyctx S) n :
  typed_glued Ω (LitNat n) tInt
| typed_BoolG {S} (Ω : tyctx S) b :
  typed_glued Ω (LitBool b) tBool
| typed_UnitG {S} (Ω : tyctx S) :
  typed_glued Ω LitUnit tUnit
.

Section glue.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS Σ, !stateG rs Σ, !heapG rs Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).

  Definition s : stuckness := λ e, e = OtherError.
  Variable p : na_inv_pool_name.
  Definition valid2 {S} (Ω : tyctx S) (α : interp_scope (E:=F) S -n> IT) (τ : ty) : iProp :=
     valid1 rs s (λ σ, has_substate σ ∗ na_own p ⊤)%I Ω α τ.

  Definition io_valid {S} (Γ : io_lang.tyctx S) α (τ' : io_lang.ty) : iProp :=
    input_lang.logpred.valid1 rs s (λ _ : unitO, na_own p ⊤) Γ α τ'.

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


  Local Opaque thunked thunkedV Thunk.
  Lemma compat_glue_to_affine_bool {S} (Ω : tyctx S) α :
    io_valid empC α Tnat ⊢
     valid2 Ω (constO (glue2_bool (α ()))) tBool.
  Proof.
    iIntros "H".
    iIntros (ss) "#Hctx Has". simpl.
    iIntros (σ) "[Hs Hp]".
    iSpecialize ("H" $! σ emp_ssubst with "Hs []").
    { unfold logpred.ssubst_valid.
      iApply ssubst_valid_nil. }
    iSpecialize ("H" $! tt with "Hp").
    simp interp_ssubst. simpl.
    iApply (wp_bind _ (IFSCtx _ _)).
    { solve_proper. }
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as (_) "[Ha Hp]".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Ha".
    iRewrite "Ha".
    unfold IFSCtx.
    iModIntro. destruct n as [|n]; simpl.
    * rewrite IF_False ; last lia.
      iApply wp_val; eauto with iFrame.
    * rewrite IF_True ; last lia.
      iApply wp_val; eauto with iFrame.
  Qed.
  Lemma compat_glue_to_affine_nat {S} (Ω : tyctx S) α :
    io_valid empC α Tnat ⊢
      valid2 Ω (constO (α ())) tInt.
  Proof.
    iIntros "H".
    iIntros (ss) "#Hctx Has". simpl.
    iIntros (σ) "[Hs Hp]".
    iSpecialize ("H" $! σ emp_ssubst with "Hs []").
    { unfold logpred.ssubst_valid.
      iApply ssubst_valid_nil. }
    iSpecialize ("H" $! tt with "Hp").
    simp interp_ssubst. simpl.
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as (_) "[Ha Hp]".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iModIntro. eauto with iFrame.

  Qed.
  Lemma compat_glue_from_affine_bool α :
    valid2 empC α tBool ⊢
      heap_ctx -∗ io_valid empC α Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (_) "Hp".
    iSpecialize ("H" $! emp_ssubst with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_nil. }
    dependent elimination ss as [emp_ssubst].
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha [Hs Hp]]".
    iModIntro. simpl. iFrame. iExists tt,_; iFrame.
    iDestruct "Ha" as "[Ha|Ha]"; iExists _; eauto.
  Qed.
  Lemma compat_glue_from_affine_nat α :
    valid2 empC α tInt ⊢
      heap_ctx -∗ io_valid empC α Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (_) "Hp".
    iSpecialize ("H" $! emp_ssubst with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_nil. }
    dependent elimination ss as [emp_ssubst].
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha [Hs Hp]]".
    iModIntro. iExists tt. eauto with iFrame.
  Qed.
  Lemma compat_glue_from_affine_unit α :
    valid2 empC α tUnit ⊢
      heap_ctx -∗ io_valid empC α Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (_) "Hp".
    iSpecialize ("H" $! emp_ssubst with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_nil. }
    dependent elimination ss as [emp_ssubst].
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha [Hs Hp]]".
    iModIntro. iExists tt. iFrame. simpl.
    iRewrite "Ha". eauto with iFrame.
  Qed.

  Local Opaque interp_tarr logpred.interp_tarr.

  Lemma compat_glue_from_affine_fun (τ1 τ2 : ty)
    (τ1' τ2' : io_lang.ty) α (glue_to_affine glue_from_affine : IT -n> IT) :
    (∀ α, io_valid empC α τ1'
            ⊢ valid2 empC (constO (glue_to_affine (α ()))) τ1) →
    (∀ α,  valid2 empC (constO α) τ2
             ⊢ heap_ctx -∗ io_valid empC (constO (glue_from_affine α)) τ2') →
    valid2 empC (constO α) (tArr τ1 τ2)
    ⊢ heap_ctx -∗
      io_valid empC
         (constO (glue_from_affine_fun glue_from_affine glue_to_affine α))
         (Tarr (Tarr Tnat τ1') τ2').
  Proof.
    intros G1 G2.
    iIntros "H #Hctx". iIntros (σ ss) "Hs _ _ Hp".
    simpl. clear ss.
    iSpecialize ("H" $! emp_ssubst with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_nil. }
    simpl. iApply wp_let.
    { solve_proper. }
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha [Hs Hp]]".
    iSimpl in "Ha".
    iSimpl. iModIntro.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    { solve_proper_please. }
    iNext. iIntros (l) "Hl".
    iApply fupd_wp.
    { solve_proper. }
    iMod (na_inv_alloc p _ (nroot.@"yolo")
            (pointsto l (Nat 1) ∨
               (pointsto l (Nat 0) ∗ interp_tarr (interp_ty τ1) (interp_ty τ2) αv)) with "[Hl Ha]") as "#Hinv".
    { iNext. iRight. iFrame. }
    iModIntro. simpl. iApply wp_val.
    iModIntro. iExists tt. iFrame. iExists σ'. iFrame.
    iModIntro. clear σ σ'. iIntros (σ βv) "Hs #Hb".
    iIntros (_) "Hp".
    iApply wp_lam. iNext. simpl.
    iApply wp_let.
    { solve_proper. }
    iApply wp_lam. iNext. simpl.
    iApply (wp_bind _ (IFSCtx _ _)).
    { solve_proper_please. }
    iApply fupd_wp.
    { solve_proper. }
    iMod  (na_inv_acc with "Hinv Hp")
      as "[Hl [Hp Hcl]]"; [ set_solver | set_solver | ].
    iModIntro.
    iDestruct "Hl" as "[Hl | [Hl Ha]]".
    * iApply (wp_read with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val.
      iModIntro.
      unfold IFSCtx. simpl.
      rewrite IF_True; last lia.
      iApply wp_err. done.
    * iApply (wp_read with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val.
      iModIntro.
      unfold IFSCtx. simpl.
      rewrite IF_False; last lia.
      iApply wp_seq.
      { solve_proper_please. }
      iApply (wp_write with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val.
      iMod ("Hcl" with "[Hl $Hp]") as "Hp".
      { iNext. iLeft; eauto. }
      iModIntro.
      iApply wp_let.
      { solve_proper. }
      iSpecialize ("Hb" $! _ (NatV 0) with "Hs []").
      { eauto with iFrame. }
      iSpecialize ("Hb" $! tt with "Hp").
      iApply (wp_wand with "Hb").
      iIntros (γv). iDestruct 1 as (_) "[Hg Hp]".
      iDestruct "Hg" as (σ') "[Hg Hst]".
      iModIntro. simpl.
      iApply wp_let.
      { solve_proper. }
      iPoseProof (G1 (constO (IT_of_V γv))) as "G1".
      iSpecialize ("G1" with "[Hg]").
      { iIntros (σ0 ss0) "Hs Has". simpl.
        iApply expr_pred_ret. simpl. eauto with iFrame. }
      iSpecialize ("G1" $! emp_ssubst with "Hctx [] [$Hst $Hp]").
      { iApply ssubst_valid_nil. }
      iApply (wp_wand with "G1").
      clear βv σ'.
      iIntros (βv). iDestruct 1 as (σ') "[Hb [Hst Hp]]".
      iModIntro. simpl.
      iApply wp_let.
      { solve_proper. }
      iSpecialize ("Ha" with "Hb [$Hst $Hp]").
      iApply (wp_wand with "Ha").
      clear γv σ'.
      iIntros (γv). iDestruct 1 as (σ') "[Hg [Hst Hp]]".
      iModIntro.
      iPoseProof (G2 (IT_of_V γv)) as "G1".
      iSpecialize ("G1" with "[Hg] Hctx").
      { iIntros (ss0) "_ _".
        by iApply expr_pred_ret. }
      iSpecialize ("G1" $! _ emp_ssubst with  "Hst []").
      { iApply ssubst_valid_nil. }
      iApply ("G1" $! tt with "Hp").
  Qed.

  Lemma compat_glue_to_affine_fun {S} (Ω : tyctx S) (τ1 τ2 : ty)
    (τ1' τ2' : io_lang.ty) α (glue_to_affine glue_from_affine : IT -n> IT) :
    (∀ α, io_valid empC α τ2'
            ⊢ valid2 Ω (constO (glue_to_affine (α ()))) τ2) →
    (∀ α,  valid2 empC (constO α) τ1
             ⊢ heap_ctx -∗ io_valid empC (constO (glue_from_affine α)) τ1') →
    io_valid empC α (Tarr (Tarr Tnat τ1') τ2')
      ⊢ valid2 Ω
      (constO (glue_to_affine_fun glue_from_affine glue_to_affine (α ())))
      (tArr τ1 τ2).
  Proof.
    intros G1 G2.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iIntros (σ) "[Hs Hp]". simpl.
    iSpecialize ("H" $! _ emp_ssubst with "Hs []").
    { iApply ssubst_valid_nil. }
    iSpecialize ("H" $! tt with "Hp").
    simp interp_ssubst. simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as (_) "[Ha Hp]".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    simpl. iModIntro.
    iApply wp_val. iModIntro.
    iExists σ'. iFrame.
    iIntros (βv) "Hb".
    (* preparing a thunk *)
    iSimpl. clear σ σ'.
    iIntros (σ) "[Hs Hp]".
    iApply (wp_bind _ (AppRSCtx _)).
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    { solve_proper. }
    iNext. iIntros (l) "Hl".
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
    iApply wp_let.
    { solve_proper. }
    iPoseProof (G2 (IT_of_V βv)) as "G2".
    iSpecialize ("G2" with "[Hb]").
    { iIntros (ss) "Hss _".
      iIntros (σ0) "Hs". simpl.
      iApply wp_val. eauto with iFrame. }
    iSpecialize ("G2" with "Hctx").
    iSpecialize ("G2" $! _ emp_ssubst with "Hs []").
    { iApply ssubst_valid_nil. }
    iSpecialize ("G2" $! tt with "Hp").
    iApply (wp_wand with "G2").
    iIntros (β'v).
    iDestruct 1 as (_) "[Hb Hp]". iModIntro.
    simpl. clear σ. iDestruct "Hb" as (σ) "[#Hb Hs]".
    (* calling the original function *)
    iApply wp_let.
    { solve_proper. }
    iApply (wp_bind _ (AppRSCtx _)).
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    { solve_proper. }
    iNext. iIntros (l') "Hl'".
    unfold AppRSCtx.
    iClear "Hl". clear l.
    iApply fupd_wp.
    { solve_proper. }
    iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Nat n)) with "[Hl']") as "#Hinv".
    { iNext. iExists _; done. }
    iPoseProof ("Ha" $! _ (thunkedV (IT_of_V β'v) l') with "Hs [-Has Hp]") as "H1".
    { iModIntro. iIntros (σ' βn) "Hs Hbm".
      iDestruct "Hbm" as (m) "Hbm".
      iIntros (_) "Hp".
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
        iModIntro. iExists tt. eauto with iFrame.
      - rewrite IF_True; last lia.
        iApply wp_err. done. }
    iModIntro.
    iSpecialize ("H1" $! tt with "Hp").
    iApply (wp_wand with "H1").
    iIntros (γv). iDestruct 1 as (_) "[H2 Hp]".
    iModIntro. simpl. iDestruct "H2" as (σ') "[#H2 Hs]".
    iPoseProof (G1 (constO (IT_of_V γv))) as "G1".
    iSpecialize ("G1" with "[H2]").
    { iIntros (σ0 ss0) "Hs Has". simpl.
      iApply expr_pred_ret. simpl.
      eauto with iFrame. }
    iSpecialize ("G1" with "Hctx Has").
    iSpecialize ("G1" with "[$Hs $Hp]").
    simpl. done.
  Qed.

  Lemma glue_to_affine_compatibility {S} (Ω : tyctx S) (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') α :
    io_valid empC α τ1' ⊢ valid2 Ω (constO (glue_to_affine Hconv (α ()))) τ1
  with glue_from_affine_compatibility (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') (α : IT) :
    valid2 empC (constO α) τ1 ⊢ heap_ctx -∗ io_valid empC (constO (glue_from_affine Hconv α)) τ1'.
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
      + simpl. iApply compat_glue_from_affine_fun.
        * apply glue_to_affine_compatibility.
        * apply glue_from_affine_compatibility.
  Qed.

  Definition interp_typed_expr {S} {Ω : tyctx S} (e : expr S) {τ}
     (typed : typed_glued Ω e τ) : interp_scope (E:=F) S -n> IT.
  Proof using rs subReifier0 subReifier1 sz.
    induction typed.
    (** glue *)
    - refine (constO $ glue_to_affine t (io_lang.interp_closed _ e)).
    (** functions *)
    - refine (Force ◎ interp_var v).
    - refine (interp_lam _ IHtyped).
    - refine (interp_app _ IHtyped1 IHtyped2 ◎ interp_scope_split).
    (** pairs *)
    - refine (interp_pair _ IHtyped1 IHtyped2 ◎ interp_scope_split).
    - refine (interp_destruct _ IHtyped1 IHtyped2 ◎ interp_scope_split).
    (** references *)
    - refine (interp_alloc  _ IHtyped).
    - refine (interp_replace _ IHtyped1 IHtyped2 ◎ interp_scope_split).
    - refine (interp_dealloc _ IHtyped).
    (** literals *)
    - refine (interp_litnat _ n).
    - refine (interp_litbool _ b).
    - refine (interp_litunit _).
  Defined.

  Lemma fundamental_affine_glued {S} (Ω : tyctx S) (e : expr S) τ :
    ∀ (typed : typed_glued Ω e τ),
    ⊢ valid2 Ω (interp_typed_expr e typed) τ.
  Proof.
    intros typed. induction typed; simpl.
    - iApply glue_to_affine_compatibility.
      by iApply fundamental.
    - by iApply compat_var.
    - by iApply compat_lam.
    - by iApply compat_app.
    - by iApply compat_pair.
    - by iApply compat_destruct.
    - by iApply compat_alloc.
    - by iApply compat_replace.
    - by iApply compat_dealloc.
    - by iApply compat_nat.
    - by iApply compat_bool.
    - by iApply compat_unit.
  Qed.

End glue.
