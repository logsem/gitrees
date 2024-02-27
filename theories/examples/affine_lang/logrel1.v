(** Unary (Kripke) logical relation for the affine lang *)
From gitrees Require Export gitree program_logic greifiers.
From gitrees.examples.affine_lang Require Import lang.
From gitrees.effects Require Import store.
From gitrees.lib Require Import pairs.
From gitrees.utils Require Import finite_sets.


Inductive typed : forall {S : Set}, (S → ty) → expr S → ty → Prop :=
(** functions *)
| typed_Var {S : Set} (Ω : S → ty) (v : S)  :
  typed Ω (Var v) (Ω v)
| typed_Lam {S : Set} (Ω : S → ty) (τ1 τ2 : ty) (e : expr (inc S) ) :
  typed (Ω ▹ τ1) e τ2 →
  typed Ω (Lam e) (tArr τ1 τ2)
| typed_App {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tArr τ1 τ2) →
  typed Ω2 e2 τ1 →
  typed (sum_map' Ω1 Ω2) (App e1 e2) τ2
(** pairs *)
| typed_Pair {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 τ1 →
  typed Ω2 e2 τ2 →
  typed (sum_map' Ω1 Ω2) (EPair e1 e2) (tPair τ1 τ2)
| typed_Destruct {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 τ : ty)
  (e1 : expr S1) (e2 : expr (inc (inc S2))) :
  typed Ω1 e1 (tPair τ1 τ2) →
  typed ((Ω2 ▹ τ2) ▹ τ1) e2 τ →
  typed (sum_map' Ω1 Ω2) (EDestruct e1 e2) τ
(** references *)
| typed_Alloc {S : Set} (Ω : S → ty) τ e :
  typed Ω e τ →
  typed Ω (Alloc e) (tRef τ)
| typed_Replace {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tRef τ1) →
  typed Ω2 e2 τ2 →
  typed (sum_map' Ω1 Ω2) (Replace e1 e2) (tPair τ1 (tRef τ2))
| typed_Dealloc {S : Set} (Ω : S → ty) e τ :
  typed Ω e (tRef τ) →
  typed Ω (Dealloc e) tUnit
(** literals *)
| typed_Nat {S : Set} (Ω : S → ty) n :
  typed Ω (LitNat n) tInt
| typed_Bool {S : Set} (Ω : S → ty) b :
  typed Ω (LitBool b) tBool
| typed_Unit {S : Set} (Ω : S → ty) :
  typed Ω LitUnit tUnit
.

Section logrel.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier input_lang.interp.reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
  Notation iProp := (iProp Σ).

  (* parameters for the kripke logical relation *)
  Variable s : stuckness.
  Context `{A:ofe}.
  Variable (P : A -n> iProp).
  Local Notation expr_pred := (expr_pred s rs P).

  (* interpreting tys *)
  Program Definition protected (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (WP@{rs} Force (IT_of_V αv) @ s {{ Φ }})%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tbool : ITV -n> iProp := λne αv,
    (αv ≡ RetV 0 ∨ αv ≡ RetV 1)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n : nat, αv ≡ RetV n)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tunit : ITV -n> iProp := λne αv,
    (αv ≡ RetV ())%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tpair (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ β1v β2v, IT_of_V αv ≡ pairITV (IT_of_V β1v) (IT_of_V β2v) ∗
                  Φ1 β1v ∗ Φ2 β2v)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∀ βv, Φ1 βv -∗ expr_pred ((IT_of_V αv) ⊙ (Thunk (IT_of_V βv))) Φ2)%I.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_ref (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ (l : loc), αv ≡ RetV l ∗ ∃ βv, pointsto l (IT_of_V βv) ∗ Φ βv)%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tBool => interp_tbool
    | tUnit => interp_tunit
    | tInt  => interp_tnat
    | tPair τ1 τ2 => interp_tpair (interp_ty τ1) (interp_ty τ2)
    | tArr τ1 τ2 => interp_tarr  (interp_ty τ1) (interp_ty τ2)
    | tRef τ => interp_ref (interp_ty τ)
    end.

  Notation ssubst_valid := (ssubst_valid_fin1 rs ty (λ x, protected (interp_ty x)) expr_pred).

  Definition valid1 {S : Set} `{!EqDecision S} `{!Finite S} (Ω : S → ty)
    (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    ∀ ss, heap_ctx
          -∗ (ssubst_valid Ω ss)
          -∗ expr_pred (α ss) (interp_ty τ).

  Lemma compat_pair {S1 S2 : Set}
    `(!EqDecision S1) `(!Finite S1)
    `(!EqDecision S2) `(!Finite S2)
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty) α β τ1 τ2 :
    ⊢ valid1 Ω1 α τ1 -∗
      valid1 Ω2 β τ2 -∗
      valid1 (sum_map' Ω1 Ω2) (interp_pair α β ◎ interp_scope_split) (tPair τ1 τ2).
  Proof.
    Opaque pairITV.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_pair].
    rewrite ssubst_valid_fin_app1.
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
    simpl.
    iExists _,_.
    by iFrame.
  Qed.

  Lemma compat_destruct {S1 S2 : Set}
    `(!EqDecision S1) `(!Finite S1)
    `(!EqDecision S2) `(!Finite S2)
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty)
    α β τ1 τ2 τ :
    ⊢ valid1 Ω1 α (tPair τ1 τ2)
      -∗ valid1 (Ω2 ▹ τ2 ▹ τ1) β τ
      -∗ valid1 (sum_map' Ω1 Ω2) (interp_destruct α β ◎ interp_scope_split) τ.
  Proof.
    Opaque pairITV thunked thunkedV projIT1 projIT2.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_destruct].
    rewrite ssubst_valid_fin_app1.
    iDestruct "Has" as "[Ha1 Ha2]".
    iSpecialize ("H1"  with "Hctx Ha1").
    iApply (expr_pred_bind (LETCTX _) with "H1").
    iIntros (αv) "Ha". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iDestruct "Ha" as (β1 β2) "[#Ha [Hb1 Hb2]]".
    iIntros (x) "Hx".
    iApply wp_let.
    iApply (wp_Thunk with "Hctx").
    {
      repeat intro; simpl.
      repeat f_equiv.
      intro; simpl.
      f_equiv.
      intro B; simpl.
      destruct B as [| [|]]; [by f_equiv | reflexivity | reflexivity].
    }
    iNext. iIntros (l1) "Hl1". simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    {
      repeat intro; simpl.
      repeat f_equiv.
      intro B; simpl.
      destruct B as [| [|]]; [reflexivity | by f_equiv | reflexivity].
    }
    iNext. iIntros (l2) "Hl2". simpl.
    pose (ss' := (extend_scope
                    (extend_scope
                       (interp_scope_split αs).2
                       (IT_of_V (thunkedV (projIT2 (IT_of_V αv)) l2)))
                    (IT_of_V (thunkedV (projIT1 (IT_of_V αv)) l1)))).
    iSpecialize ("H2" $! ss'
                  with "Hctx [-Hx] Hx").
    {
      iApply ssubst_valid_fin_cons1.
      iSplitR "Hl1 Hb1".
      - iApply ssubst_valid_fin_cons1.
        iSplitL "Ha2"; first done.
        Transparent thunkedV thunked.
        simpl.
        iIntros (z) "Hz".
        simpl.
        iApply wp_val.
        iModIntro.
        iExists z; iFrame.
        iApply wp_lam.
        iNext.
        simpl.
        iApply (wp_bind _ (IFSCtx _ _)).
        iApply (wp_read with "Hctx Hl2").
        iNext. iNext. iIntros "Hl2".
        iApply wp_val. iModIntro.
        unfold IFSCtx. simpl.
        rewrite IF_False; last lia.
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write with "Hctx Hl2").
        iNext. iNext. iIntros "Hl2".
        iRewrite "Ha".
        simpl.
        rewrite projIT2_pairV.
        do 3 (iApply wp_tick; iNext).
        iApply wp_val. iModIntro.
        iApply "Hb2".
      - Transparent thunkedV thunked.
        simpl.
        iIntros (z) "Hz".
        simpl.
        iApply wp_val.
        iModIntro.
        iExists z; iFrame.
        iApply wp_lam.
        iNext.
        simpl.
        iApply (wp_bind _ (IFSCtx _ _)).
        iApply (wp_read with "Hctx Hl1").
        iNext. iNext. iIntros "Hl1".
        iApply wp_val. iModIntro.
        unfold IFSCtx. simpl.
        rewrite IF_False; last lia.
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write with "Hctx Hl1").
        iNext. iNext. iIntros "Hl1".
        iRewrite "Ha".
        simpl.
        rewrite projIT1_pairV.
        do 3 (iApply wp_tick; iNext).
        iApply wp_val. iModIntro.
        iApply "Hb1".
    }
    iApply "H2".
  Qed.

  Lemma compat_alloc {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) α τ:
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
    iExists l.
    iSplit; first done.
    iExists αv.
    iFrame "Hl".
    iFrame.
  Qed.

  Lemma compat_replace {S1 S2 : Set}
    `(!EqDecision S1) `(!Finite S1)
    `(!EqDecision S2) `(!Finite S2)
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty) α β τ τ' :
    ⊢ valid1 Ω1 α (tRef τ) -∗
      valid1 Ω2 β τ' -∗
      valid1 (sum_map' Ω1 Ω2) (interp_replace α β ◎ interp_scope_split) (tPair τ (tRef τ')).
  Proof.
    Opaque pairITV.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    cbn-[interp_replace].
    rewrite ssubst_valid_fin_app1.
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1"  with "Hctx Ha1").
    iSpecialize ("H2"  with "Hctx Ha2").
    iApply (expr_pred_bind (LETCTX _) with "H2").
    iIntros (βv) "Hb". unfold LETCTX. simpl.
    rewrite LET_Val/=.
    iApply (expr_pred_bind with "H1").
    iIntros (αv) "Ha". simpl.
    iDestruct "Ha" as (l) "[Ha Ha']".
    iDestruct "Ha'" as (γ) "[Hl Hg]".
    iApply expr_pred_frame.
    iRewrite "Ha". simpl.
    rewrite IT_of_V_Ret.
    rewrite -> get_ret_ret; simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_read with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    simpl. iApply wp_seq.
    { solve_proper. }
    iApply (wp_write with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    rewrite get_val_ITV. simpl.
    rewrite get_val_ITV. simpl.
    iApply wp_val. iModIntro.
    iExists γ, (RetV l).
    iSplit; first done.
    iFrame. eauto with iFrame.
  Qed.

  Lemma compat_dealloc {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) α τ:
    ⊢ valid1 Ω α (tRef τ) -∗
      valid1 Ω (interp_dealloc α) tUnit.
  Proof.
    iIntros "H".
    iIntros (αs) "#Hctx Has".
    iSpecialize ("H" with "Hctx Has").
    iApply (expr_pred_bind with "H").
    iIntros (αv) "Ha /=".
    iDestruct "Ha" as (l) "[Ha Ha']".
    iDestruct "Ha'" as (βv) "[Hl Hb]".
    iRewrite "Ha". iApply expr_pred_frame. simpl.
    rewrite IT_of_V_Ret. rewrite -> get_ret_ret. simpl.
    iApply (wp_dealloc with "Hctx Hl").
    iNext. iNext. eauto with iFrame.
  Qed.

  Lemma compat_bool {S : Set}
    `{!EqDecision S} `{!Finite S}
    b (Ω : S → ty) :
    ⊢ valid1 Ω (interp_litbool b) tBool.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret.
    destruct b; simpl; eauto.
  Qed.

  Lemma compat_nat {S : Set}
    `{!EqDecision S} `{!Finite S}
    n (Ω : S → ty) :
    ⊢ valid1 Ω (interp_litnat n) tInt.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret. eauto with iFrame.
  Qed.

  Lemma compat_unit {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) :
    ⊢ valid1 Ω interp_litunit tUnit.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret. eauto with iFrame.
  Qed.

  Lemma compat_var {S : Set}
    `{!EqDecision S} `{!Finite S}
    Ω (v : S) :
    ⊢ valid1 Ω (Force ◎ interp_var v) (Ω v).
  Proof.
    iIntros (ss) "#Hctx Has".
    iIntros (x) "Hx".
    unfold Force.
    simpl.
    iApply (wp_bind rs (AppRSCtx (ss v))).
    { solve_proper. }
    iApply wp_val.
    iModIntro.
    unfold AppRSCtx.
    iApply (wp_bind rs (AppLSCtx (IT_of_V (RetV 0)))).
    { solve_proper. }
    unfold AppLSCtx.
    simpl.
    iDestruct (ssubst_valid_fin_lookup1 _ _ _ _ _ _ v with "Has Hx") as "Has".
    iApply (wp_wand with "Has").
    iIntros (w) "(%y & Hw1 & Hw2)"; simpl.
    iModIntro.
    rewrite IT_of_V_Ret.
    iApply (wp_wand with "Hw1 [Hw2]").
    iIntros (z) "Hz".
    iModIntro.
    iExists y.
    iFrame.
  Qed.

  Lemma compat_app {S1 S2 : Set}
    `(!EqDecision S1) `(!Finite S1)
    `(!EqDecision S2) `(!Finite S2)
    `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)}
    (Ω1 : S1 → ty) (Ω2 : S2 → ty)
    α β τ1 τ2 :
    ⊢ valid1 Ω1 α (tArr τ1 τ2) -∗
      valid1 Ω2 β τ1 -∗
      valid1 (sum_map' Ω1 Ω2) (interp_app α β ◎ interp_scope_split) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (αs) "#Hctx Has".
    iEval(cbn-[interp_app]).
    rewrite ssubst_valid_fin_app1.
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

  Lemma compat_lam {S : Set}
    `{!EqDecision S} `{!Finite S}
    (Ω : S → ty) τ1 τ2 α :
    ⊢ valid1 (Ω ▹ τ1) α τ2 -∗
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
    Local Transparent Thunk.
    Local Opaque thunked thunkedV.
    iSimpl. iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    unfold AppRSCtx.
    iApply wp_lam. iNext.
    iEval(cbn-[thunked]).
    pose (ss' := extend_scope αs (IT_of_V (thunkedV (IT_of_V βv) l))).
    iSpecialize ("H" $! ss'
             with "Hctx [-Hx] Hx").
    {
      iApply ssubst_valid_fin_cons1.
      iFrame "Has".
      Local Transparent thunked thunkedV.
      simpl.
      iIntros (x') "Hx".
      iApply wp_val.
      iModIntro.
      iExists x'.
      iFrame "Hx".
      iApply wp_lam.
      iNext.
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
      iApply "Hb".
    }
    iApply "H".
  Qed.

  Lemma fundamental_affine (S : Set)
    (HE : EqDecision S) (HF : Finite S)
    (Ω : S → ty)
    (e : expr S) τ :
    typed Ω e τ →
    ⊢ valid1 Ω (interp_expr _ e) τ.
  Proof.
    intros H.
    iStartProof.
    iInduction H as [| | | | | | | | | |] "IH".
    - by iApply compat_var.
    - by iApply compat_lam.
    - by iApply (compat_app EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
    - by iApply (compat_pair EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
    - by iApply (compat_destruct EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
    - by iApply compat_alloc.
    - by iApply (compat_replace EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight).
    - by iApply compat_dealloc.
    - by iApply compat_nat.
    - by iApply compat_bool.
    - by iApply compat_unit.
  Qed.

End logrel.

Arguments interp_tarr {_ _ _ _ _ _ _ _ _ _ _ _ _} Φ1 Φ2.
Arguments interp_tbool {_ _ _ _ _ _}.
Arguments interp_tnat {_ _ _ _ _ _}.
Arguments interp_tunit {_ _ _ _ _ _}.
Arguments interp_ty {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} τ.

Arguments compat_app {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments compat_pair {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments compat_destruct {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.
Arguments compat_replace {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Local Definition rs : gReifiers NotCtxDep 2 :=
  gReifiers_cons reify_store (gReifiers_cons input_lang.interp.reify_io gReifiers_nil).

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logrel1_adequacy cr Σ R `{!Cofe R, !SubOfe natO R, !SubOfe unitO R, !SubOfe locO R} `{!invGpreS Σ}
  `{!statePreG rs R Σ} `{!heapPreG rs R Σ} τ
  (α : interp_scope ∅ -n>  IT (gReifiers_ops rs) R) (β : IT (gReifiers_ops rs) R) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ},
      (£ cr ⊢ valid1 rs notStuck (λne _: unitO, True)%I □ α τ)%I) →
  ssteps (gReifiers_sReifier rs) (α ı_scope) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (∃ βv, (IT_of_V βv ≡ β)%stdpp).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
      ∨ (∃ e, (β ≡ Err e)%stdpp ∧ notStuck e)).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety (S cr)); eauto.
  { apply Hdisj. }
  { by rewrite Hb. }
  intros H1 H2.
  exists (λ _, True)%I. split.
  { apply _. }
  iIntros "[[Hone Hcr] Hst]".
  pose (σ := st.1).
  pose (ios := st.2.1).
  iMod (new_heapG rs σ) as (H3) "H".
  iAssert (has_substate σ ∗ has_substate ios)%I with "[Hst]" as "[Hs Hio]".
  { unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) _) st ≡
            of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state σ)
            ⋅ of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state ios))%stdpp as ->; last first.
    { rewrite -own_op. done. }
    unfold sR_idx. simpl.
    intro j.
    rewrite discrete_fun_lookup_op.
    inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 0%fin)). done. }
    intros j. inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 1%fin)). done. }
    intros i. inversion i. }
  iApply fupd_wp.
  iMod (inv_alloc (nroot.@"storeE") _ (∃ σ, £ 1 ∗ has_substate σ ∗ own (heapG_name rs) (●V σ))%I with "[-Hcr]") as "#Hinv".
  { iNext. iExists _. iFrame. }
  simpl.
  iPoseProof (@Hlog _ _ _ with "Hcr") as "Hlog".
  iSpecialize ("Hlog" $! ı_scope with "Hinv []").
  { iApply ssubst_valid_fin_empty1. }
  iSpecialize ("Hlog" $! tt with "[//]").
  iModIntro.
  iApply (wp_wand with "Hlog").
  eauto with iFrame.
Qed.

Definition R := sumO locO (sumO unitO natO).

Lemma logrel1_safety e τ (β : IT (gReifiers_ops rs) R) st st' k :
  typed □ e τ →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (∃ βv, (IT_of_V βv ≡ β)%stdpp).
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs R;heapΣ rs R]).
  eapply (logrel1_adequacy 0 Σ); eauto; try apply _.
  iIntros (? ? ?) "_".
  iApply (fundamental_affine rs notStuck (λne _ : unitO, True)%I).
  apply Hty.
Qed.
