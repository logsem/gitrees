(** Unary (Kripke) logical relation for the affine lang *)
From Equations Require Import Equations.
From gitrees Require Export lang_affine gitree program_logic.
From gitrees.affine_lang Require Import lang.
From gitrees.examples Require Import store pairs.
Require Import iris.algebra.gmap.

Local Notation tyctx := (tyctx ty).

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

Section logrel.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier input_lang.interp.reify_io rs}.
  Notation F := (gReifiers_ops NotCtxDep rs).
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
    (∃ (l : loc) βv, αv ≡ RetV l ∗ pointsto l (IT_of_V βv) ∗ Φ βv)%I.
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
    lang_affine.ssubst_valid rs (λ τ, protected (interp_ty τ)) Ω ss.

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
    iExists γ,(RetV l).
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
    rewrite IT_of_V_Ret. rewrite -> get_ret_ret. simpl.
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
    ⊢ valid1 Ω (interp_expr _ e) τ.
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

End logrel.

Arguments interp_tarr {_ _ _ _ _ _ _ _ _ _ _ _ _} Φ1 Φ2.
Arguments interp_tbool {_ _ _ _ _ _}.
Arguments interp_tnat {_ _ _ _ _ _}.
Arguments interp_tunit {_ _ _ _ _ _}.
Arguments interp_ty {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} τ.

Local Definition rs : gReifiers NotCtxDep 2 :=
  gReifiers_cons NotCtxDep reify_store (gReifiers_cons NotCtxDep input_lang.interp.reify_io (gReifiers_nil NotCtxDep)).

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logrel1_adequacy cr Σ R `{!Cofe R, !SubOfe natO R, !SubOfe unitO R, !SubOfe locO R} `{!invGpreS Σ}
  `{!statePreG rs R Σ} `{!heapPreG rs R Σ} τ
  (α : unitO -n>  IT (gReifiers_ops NotCtxDep rs) R) (β : IT (gReifiers_ops NotCtxDep rs) R) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ},
      (£ cr ⊢ valid1 rs notStuck (λne _: unitO, True)%I empC α τ)%I) →
  ssteps (gReifiers_sReifier NotCtxDep rs) (α ()) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier NotCtxDep rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier NotCtxDep rs) β st' β1 st1)
      ∨ (∃ e, β ≡ Err e ∧ notStuck e)).
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
    assert (of_state NotCtxDep rs (IT (gReifiers_ops NotCtxDep rs) _) st ≡
            of_idx NotCtxDep rs (IT (gReifiers_ops NotCtxDep rs) _) sR_idx (sR_state σ)
            ⋅ of_idx NotCtxDep rs (IT (gReifiers_ops NotCtxDep rs) _) sR_idx (sR_state ios)) as ->; last first.
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
  iSpecialize ("Hlog" $! emp_ssubst with "Hinv []").
  { iApply ssubst_valid_nil. }
  iSpecialize ("Hlog" $! tt with "[//]").
  iModIntro.
  iApply (wp_wand with "Hlog").
  eauto with iFrame.
Qed.

Definition R := sumO locO (sumO unitO natO).

Lemma logrel1_safety e τ (β : IT (gReifiers_ops NotCtxDep rs) R) st st' k :
  typed empC e τ →
  ssteps (gReifiers_sReifier NotCtxDep rs) (interp_expr rs e ()) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier NotCtxDep rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs R;heapΣ rs R]).
  eapply (logrel1_adequacy 0 Σ); eauto; try apply _.
  iIntros (? ? ?) "_".
  by iApply fundamental_affine.
Qed.
