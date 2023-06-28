From Equations Require Import Equations.
From iris.base_logic.lib Require Import na_invariants.
From gitrees Require Export lang_generic gitree program_logic.
From gitrees.input_lang Require Import lang interp logpred.
From gitrees.affine_lang Require Import lang logrel1.
From gitrees.examples Require Import store pairs.

Local Notation tyctx := (tyctx ty).

Inductive typed_glued : forall {S}, tyctx S → expr S → ty → Type :=
(** FFI *)
| typed_Glue {S} (Ω : tyctx S) τ' τ e
  (tconv : ty_conv τ τ') :
  io_lang.typed empC e τ' →
  typed_glued Ω (EEmbed e tconv) τ
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

Local Arguments logpred.interp_tarr {_ _ _ _ _ _ _ _ _}.
Local Arguments logpred.interp_ty {_ _ _ _ _ _ _ _ _} _.

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

  Local Opaque thunked thunkedV Thunk.
  Lemma compat_glue_to_affine_bool {S} (Ω : tyctx S) α :
    io_valid empC α Tnat ⊢
     valid2 Ω (constO (glue2_bool _ (α ()))) tBool.
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
         (constO (glue_from_affine_fun _ glue_from_affine glue_to_affine α))
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
      (constO (glue_to_affine_fun _ glue_from_affine glue_to_affine (α ())))
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
    io_valid empC α τ1' ⊢ valid2 Ω (constO (glue_to_affine _ Hconv (α ()))) τ1
  with glue_from_affine_compatibility (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') (α : IT) :
    valid2 empC (constO α) τ1 ⊢ heap_ctx -∗ io_valid empC (constO (glue_from_affine _ Hconv α)) τ1'.
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

  Lemma fundamental_affine_glued {S} (Ω : tyctx S) (e : expr S) τ :
    typed_glued Ω e τ →
    ⊢ valid2 Ω (interp_expr _ e) τ.
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
