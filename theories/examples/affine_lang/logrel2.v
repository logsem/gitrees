From iris.base_logic.lib Require Import na_invariants.
From gitrees Require Export gitree program_logic greifiers.
From gitrees.examples.input_lang Require Import lang interp logpred.
From gitrees.examples.affine_lang Require Import lang logrel1.
From gitrees.effects Require Import store fork.
From gitrees.lib Require Import pairs.
From gitrees.utils Require Import finite_sets.

Require Import Binding.Lib Binding.Set Binding.Env.

Import IF_nat.

Inductive typed_glued : forall {S : Set}, (S → ty) → expr S → ty → Type :=
(** FFI *)
| typed_Glue {S : Set} (Ω : S → ty) τ' τ e
  (tconv : ty_conv τ τ') :
  io_lang.typed □ e τ' →
  typed_glued Ω (EEmbed e tconv) τ
(** functions *)
| typed_VarG {S : Set} (Ω : S → ty) (τ : ty) (v : S)  :
  typed_glued Ω (Var v) (Ω v)
| typed_LamG {S : Set} (Ω : S → ty) (τ1 τ2 : ty) (e : expr (inc S) ) :
  typed_glued (Ω ▹ τ1) e τ2 →
  typed_glued Ω (Lam e) (tArr τ1 τ2)
| typed_AppG {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω1 e1 (tArr τ1 τ2) →
  typed_glued Ω2 e2 τ1 →
  typed_glued (sum_map' Ω1 Ω2) (App e1 e2) τ2
(** pairs *)
| typed_PairG {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω1 e1 τ1 →
  typed_glued Ω2 e2 τ2 →
  typed_glued (sum_map' Ω1 Ω2) (EPair e1 e2) (tPair τ1 τ2)
| typed_DestructG {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 τ : ty)
  (e1 : expr S1) (e2 : expr (inc (inc S2))) :
  typed_glued Ω1 e1 (tPair τ1 τ2) →
  typed_glued ((Ω2 ▹ τ2) ▹ τ1) e2 τ →
  typed_glued (sum_map' Ω1 Ω2) (EDestruct e1 e2) τ
(** references *)
| typed_AllocG {S : Set} (Ω : S → ty) τ e :
  typed_glued Ω e τ →
  typed_glued Ω (Alloc e) (tRef τ)
| typed_ReplaceG {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω1 e1 (tRef τ1) →
  typed_glued Ω2 e2 τ2 →
  typed_glued (sum_map' Ω1 Ω2) (Replace e1 e2) (tPair τ1 (tRef τ2))
| typed_DeallocG {S : Set} (Ω : S → ty) e τ :
  typed_glued Ω e (tRef τ) →
  typed_glued Ω (Dealloc e) tUnit
(** literals *)
| typed_NatG {S : Set} (Ω : S → ty) n :
  typed_glued Ω (LitNat n) tInt
| typed_BoolG {S : Set} (Ω : S → ty) b :
  typed_glued Ω (LitBool b) tBool
| typed_UnitG {S : Set} (Ω : S → ty) :
  typed_glued Ω LitUnit tUnit
(** concurrency *)
| typed_ForkG {S1 S2 : Set} (Ω1 : S1 → ty) (Ω2 : S2 → ty) e1 e2 τ :
  typed_glued Ω1 e1 tUnit →
  typed_glued Ω2 e2 τ →
  typed_glued (sum_map' Ω1 Ω2) (EFork e1 e2) τ
.

Section glue.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_fork rs}.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!na_invG Σ, !heapG rs R Σ, !gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Definition s : stuckness := λ e, (e ≡ OtherError)%stdpp.

  Definition valid2 {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty)
    (α : interp_scope (E:=F) S -n> IT)
    (τ : ty) : iProp :=
    io_ctx rs -∗ valid1 rs s (λne _ : unitO, True)%I Ω α τ.

  Definition io_valid {S : Set} (Γ : S → io_lang.ty) α (τ' : io_lang.ty)
    : iProp :=
    fork_ctx rs -∗ input_lang.logpred.valid1 rs s (λne _ : unitO, True)%I Γ α τ'.

  Local Opaque thunked thunkedV Thunk.

  Lemma compat_glue_to_affine_bool {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) α :
    io_valid □ α Tnat ⊢
     valid2 Ω (constO (glue2_bool _ (α ı_scope))) tBool.
  Proof.
    iIntros "H #Hinv".
    iIntros (ss) "#Hctx Has #Hf". simpl.
    iIntros ([]) "_".
    iSpecialize ("H" with "Hf").
    iSpecialize ("H" $! ı_scope with "Hinv []").
    { iIntros ([]). }
    iSpecialize ("H" $! tt with "[//]").
    iApply (wp_bind _ (IFSCtx _ _)).
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as ([]) "[Ha _]".
    iDestruct "Ha" as (n) "Ha".
    iRewrite "Ha".
    unfold IFSCtx.
    iModIntro. destruct n as [|n]; simpl.
    * rewrite IF_False ; last lia.
      iApply wp_val.
      iModIntro. iExists (). iSplit; first by iLeft.
      done.
    * rewrite IF_True ; last lia.
      iApply wp_val.
      iModIntro. iExists (). iSplit; first by iRight.
      done.
  Qed.

  Lemma compat_glue_to_affine_nat {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) α :
    io_valid □ α Tnat ⊢
      valid2 Ω (constO (α ı_scope)) tInt.
  Proof.
    iIntros "H #Hinv".
    iIntros (ss) "#Hctx Has #Hf". simpl.
    iSpecialize ("H" with "Hf").
    iIntros ([]) "_".
    iSpecialize ("H" $! ı_scope with "Hinv []").
    { iIntros ([]). }
    iSpecialize ("H" $! tt with "[//]").
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as ([]) "[Ha _]".
    iModIntro. iExists (). eauto with iFrame.
  Qed.

  Lemma compat_glue_from_affine_bool α :
    valid2 □ α tBool ⊢
      heap_ctx rs -∗ io_valid □ α Tnat.
  Proof.
    iIntros "H #Hctx #Hf".
    iIntros (ss) "#Hio #Hss".
    iIntros ([]) "_".
    iSpecialize ("H" with "Hio").
    iSpecialize ("H" $! ss with "Hctx [] Hf").
    { iApply ssubst_valid_fin_empty1. }
    iSpecialize ("H" $! tt with "[//]").
    iApply (wp_wand with "H").
    iIntros (αv) "Ha".
    iExists ().
    iDestruct "Ha" as ([]) "[[Ha|Ha] _]".
    - iModIntro. by iSplit; first by iExists 0.
    - iModIntro. by iSplit; first by iExists 1.
  Qed.

  Lemma compat_glue_from_affine_nat α :
    valid2 □ α tInt ⊢
      heap_ctx rs -∗ io_valid □ α Tnat.
  Proof.
    iIntros "H #Hctx #Hf".
    iIntros (ss) "#Hio #Hss".
    iIntros ([]) "_".
    iSpecialize ("H" with "Hio").
    iSpecialize ("H" $! ss with "Hctx [] Hf").
    { iApply ssubst_valid_fin_empty1. }
    iSpecialize ("H" $! tt with "[//]").
    iApply (wp_wand with "H").
    iIntros (αv) "Ha".
    iDestruct "Ha" as ([]) "[Ha _]".
    iModIntro. iExists tt. eauto with iFrame.
  Qed.

  Lemma compat_glue_from_affine_unit α :
    valid2 □ α tUnit ⊢
      heap_ctx rs -∗ io_valid □ (constO (glue_from_affine _ ty_conv_unit (α ı_scope))) Tnat.
  Proof.
    iIntros "H #Hctx #Hf".
    iIntros (ss) "#Hio #Hss".
    iIntros ([]) "_".
    iApply wp_val.
    iModIntro. iExists tt. iFrame. simpl.
    eauto with iFrame.
  Qed.

  Local Opaque interp_tarr logpred.interp_tarr.

  Lemma compat_glue_from_affine_fun (τ1 τ2 : ty)
    (τ1' τ2' : io_lang.ty) α (glue_to_affine glue_from_affine : IT -n> IT) :
    (∀ α, io_valid □ α τ1'
            ⊢ valid2 □ (constO (glue_to_affine (α ı_scope))) τ1) →
    (∀ α,  valid2 □ (constO α) τ2
             ⊢ heap_ctx rs -∗ io_valid □ (constO (glue_from_affine α)) τ2') →
    valid2 □ (constO α) (tArr τ1 τ2)
    ⊢ heap_ctx rs -∗
      io_valid □
         (constO (glue_from_affine_fun _ glue_from_affine glue_to_affine α))
         (Tarr (Tarr Tnat τ1') τ2').
  Proof.
    intros G1 G2.
    iIntros "H #Hctx #Hf".
    unfold io_valid.
    unfold logpred.valid1.
    iIntros (ss) "#Hio Hs".
    iIntros ([]) "_".
    iSpecialize ("H" with "Hio").
    iSpecialize ("H" $! ss with "Hctx [] Hf").
    { iApply ssubst_valid_fin_empty1. }
    iSpecialize ("H" $! () with "[//]").
    iApply wp_let.
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as ([]) "[Ha _]".
    iSimpl in "Ha".
    iSimpl. iModIntro.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_Thunk with "Hctx").
    { solve_proper_please. }
    iNext. iIntros (l) "Hl".
    iApply fupd_wp.
    { solve_proper. }
    iSimpl.
    iMod (inv_alloc (nroot.@"yolo") ⊤
            ((pointsto l (Ret 1))
             ∨
               (pointsto l (Ret 0) ∗ interp_tarr (interp_ty τ1) (interp_ty τ2) αv))%I
           with "[Hl Ha]") as "#Hinv".
    { iNext. iRight. by iFrame. }
    iModIntro. iApply wp_val.
    iModIntro. iExists tt.
    iSplit; last done.
    iIntros (?). iModIntro. iIntros "#Harr %_ _".
    iApply wp_lam.
    iNext. simpl. iIntros "Hcr".
    iApply wp_let.
    { solve_proper. }
    iApply wp_lam. iNext. simpl. iIntros "_".
    iApply (wp_bind _ (IFSCtx _ _)).
    { solve_proper_please. }
    iApply (xchg_wp.wp_xchg_atomic_hom rs _ (Ret 1)
              _ _ _ _ idfun with "Hctx"); first last.
    {
      iInv (nroot.@"yolo") as "J" "Hcl".
      iApply (lc_fupd_add_later with "Hcr").
      iNext.
      iDestruct "J" as "[Hl | [Hl Ha]]".
      - iModIntro.
        iExists (Ret 1).
        iFrame "Hl".
        do 2 iNext.
        iIntros "Hl".
        iSpecialize ("Hcl" with "[Hl]").
        { iNext. iLeft. iFrame "Hl". }
        iMod "Hcl".
        iModIntro.
        iApply wp_val.
        iModIntro.
        unfold IFSCtx. simpl.
        rewrite IF_True; last lia.
        iApply wp_err.
        done.
      - iModIntro.
        iExists (Ret 0).
        iFrame "Hl".
        do 2 iNext.
        iIntros "Hl".
        iApply wp_val.
        unfold IFSCtx. simpl.
        rewrite IF_False; last lia.
        iApply wp_val.
        do 2 iApply fupd_intro.
        iApply wp_let.
        { solve_proper. }
        iSpecialize ("Harr" $! (RetV 0) with "[]").
        { eauto with iFrame. }
        iSpecialize ("Harr" $! tt with "[]").
        { done. }
        iSpecialize ("Hcl" with "[Hl]").
        { iNext. iLeft. iFrame "Hl". }
        iMod "Hcl".
        iModIntro.
        iApply (wp_wand with "Harr").
        iIntros (γv). iDestruct 1 as ([]) "[Hg _]".
        iModIntro.
        iApply wp_let.
        { solve_proper. }
        iPoseProof (G1 (constO (IT_of_V γv))) as "G1".
        iSpecialize ("G1" with "[Hg]").
        {
          iIntros "#Hf'". iIntros (ss0) "_ Has". simpl.
          iApply expr_pred_ret. simpl. eauto with iFrame.
        }
        iSpecialize ("G1" with "Hio").
        iSpecialize ("G1" $! ss with "Hctx [] Hf").
        { iApply ssubst_valid_fin_empty1. }
        iSpecialize ("G1" $! () with "[//]").
        iApply (wp_wand with "G1").
        iIntros (βv'). simpl.
        iDestruct 1 as ([]) "[Hb _]".
        iModIntro. simpl.
        iApply wp_let.
        { solve_proper. }
        iSpecialize ("Ha" with "Hb").
        iSpecialize ("Ha" $! () with "[//]").
        iApply (wp_wand with "Ha").
        iIntros (γv'). iDestruct 1 as ([]) "[Hg _]".
        iModIntro.
        iPoseProof (G2 (IT_of_V γv')) as "G1".
        iSpecialize ("G1" with "[Hg] Hctx").
        {
          iIntros "_". iIntros (?) "_ _ _".
          by iApply expr_pred_ret.
        }
        iSpecialize ("G1" with "Hf").
        iSpecialize ("G1" $! ss with "Hio []").
        { iIntros ([]). }
        iSpecialize ("G1" $! () with "[//]").
        iApply ("G1").
    }
    by apply ndot_ne_disjoint.
  Qed.

  Lemma compat_glue_to_affine_fun {S : Set} `{HE : EqDecision S} `{!Finite S}
    (Ω : S → ty) (τ1 τ2 : ty)
    (τ1' τ2' : io_lang.ty) α (glue_to_affine glue_from_affine : IT -n> IT) :
    (∀ α, io_valid □ α τ2'
            ⊢ valid2 Ω (constO (glue_to_affine (α ı_scope))) τ2) →
    (∀ α,  valid2 □ (constO α) τ1
             ⊢ heap_ctx rs -∗ io_valid □ (constO (glue_from_affine α)) τ1') →
    io_valid □ α (Tarr (Tarr Tnat τ1') τ2')
      ⊢ valid2 Ω
      (constO (glue_to_affine_fun _ glue_from_affine glue_to_affine (α ı_scope)))
      (tArr τ1 τ2).
  Proof.
    intros G1 G2.
    iIntros "H".
    iIntros "#Hio". iIntros (αs) "#Hctx Has #Hf".
    iIntros (?) "_". simpl.
    iSpecialize ("H" with "Hf").
    iSpecialize ("H" $! ı_scope with "Hio []").
    { iIntros ([]). }
    iSpecialize ("H" $! tt with "[//]").
    simpl.
    iApply wp_let.
    { solve_proper. }
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as (_) "[Ha _]".
    simpl. iModIntro.
    iApply wp_val. iModIntro.
    iExists ().
    iSplit; last done.
    iIntros (βv) "Hb".
    (* preparing a thunk *)
    iSimpl.
    iIntros ([]) "_".
    iApply (wp_bind _ (AppRSCtx _)).
    iApply (wp_Thunk with "Hctx").
    { solve_proper. }
    iNext. iIntros (l) "Hl".
    unfold AppRSCtx.
    iApply wp_lam. iNext.
    iEval(cbn-[thunked]). iIntros "_".
    iApply wp_let.
    { solve_proper. }
    iApply wp_lam.
    (* forcing a thunk *)
    iNext. iSimpl. iIntros "_".
    iApply (wp_bind _ (IFSCtx _ _)).
    { solve_proper. }
    iApply (xchg_wp.wp_xchg_hom rs _ (Ret 0)
              _ _ _ idfun with "Hctx [$Hl]"); first last.
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    unfold IFSCtx. simpl.
    rewrite IF_False; last lia.
    iApply wp_val. iModIntro.
    (* doing the glue for the argument *)
    iApply wp_let.
    { solve_proper. }
    iPoseProof (G2 (IT_of_V βv)) as "G2".
    iSpecialize ("G2" with "[Hb]").
    {
      iIntros "_".
      iIntros (ss) "_ Hss _".
      iIntros (?) "_".
      simpl.
      iApply wp_val.
      iExists ().
      eauto with iFrame.
    }
    iSpecialize ("G2" with "Hctx").
    iSpecialize ("G2" with "Hf").
    iSpecialize ("G2" $! ı_scope with "Hio []").
    { iIntros ([]). }
    iSpecialize ("G2" $! tt with "[//]").
    iApply (wp_wand with "G2").
    iIntros (β'v).
    iDestruct 1 as ([]) "[#Hb _]". iModIntro.
    simpl.
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
    iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Ret n)) with "[Hl']") as "#Hinv".
    { iNext. iExists _; done. }
    iPoseProof ("Ha" $! (thunkedV (IT_of_V β'v) l') with "[-Has]") as "H1".
    {
      iModIntro. iIntros (βn) "Hbm".
      iDestruct "Hbm" as (m) "Hbm".
      iIntros ([]) "_".
      iApply wp_lam. iNext. iSimpl. iIntros "_".
      iApply (wp_bind _ (IFSCtx _ _)).
      { solve_proper. }
      iApply (xchg_wp.wp_xchg_atomic_hom rs _ (Ret 1)
                (⊤∖ nclose (nroot.@"storeE")) _ _ _ idfun with "Hctx").
      { set_solver. }
      iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
      iModIntro. iExists (Ret n). iFrame.
      iNext. iNext. iIntros "Hl'".
      iMod ("Hcl" with "[Hl']") as "_".
      { iNext. eauto with iFrame. }
      iModIntro. iApply wp_val.
      iModIntro.
      unfold IFSCtx. simpl.
      destruct n as [|n].
      - rewrite IF_False; last lia.
        iApply wp_val.
        iModIntro. iExists tt.
        iFrame "Hb".
      - rewrite IF_True; last lia.
        iApply wp_err. done.
    }
    iModIntro.
    iSpecialize ("H1" $! tt with "[//]").
    iApply (wp_wand with "H1").
    iIntros (γv). iDestruct 1 as ([]) "[#H2 _]".
    iModIntro. simpl.
    iPoseProof (G1 (constO (IT_of_V γv))) as "G1".
    iSpecialize ("G1" with "[H2]").
    {
      iIntros "_".
      iIntros (ss) "_ Has".
      simpl.
      iApply expr_pred_ret. simpl.
      eauto with iFrame.
    }
    iSpecialize ("G1" with "Hio").
    iSpecialize ("G1" $! αs with "Hctx Has Hf").
    iSpecialize ("G1" $! () with "[//]").
    simpl. done.
  Qed.

  Lemma glue_to_affine_compatibility {S : Set} `{HE : EqDecision S} `{!Finite S}
    (Ω : S → ty) (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') α :
    io_valid □ α τ1' ⊢ valid2 Ω (constO (glue_to_affine _ Hconv (α ı_scope))) τ1
  with glue_from_affine_compatibility (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') (α : IT) :
    valid2 □ (constO α) τ1 ⊢ heap_ctx rs -∗ io_valid □ (constO (glue_from_affine _ Hconv α)) τ1'.
  Proof.
    - destruct Hconv.
      + by iApply compat_glue_to_affine_bool.
      + by iApply compat_glue_to_affine_nat.
      + iIntros "_ ?".
        simpl. iApply compat_unit.
      + simpl. iApply compat_glue_to_affine_fun.
        * by apply glue_to_affine_compatibility.
        * apply glue_from_affine_compatibility.
    - destruct Hconv.
      + iApply compat_glue_from_affine_bool.
      + iApply compat_glue_from_affine_nat.
      + iApply compat_glue_from_affine_unit.
      + simpl. iApply compat_glue_from_affine_fun.
        * apply glue_to_affine_compatibility.
        * apply glue_from_affine_compatibility.
  Qed.

  Ltac fold_interp :=
    match goal with
    | |- context G [interp_expr ?a ?b] =>
        progress fold (interp_expr (R := R) a b)
    end.

  Lemma fundamental_affine_glued {S : Set} `{HE : EqDecision S} `{!Finite S}
    (Hfork : ⊢ fork_post (RetV ())) (Ω : S → ty) (e : expr S) τ :
    typed_glued Ω e τ →
    ⊢ valid2 Ω (interp_expr _ e) τ.
  Proof.
    intros typed.
    iStartProof.
    iInduction typed as [| | | | | | | | | | | |] "IH";
      first (iApply glue_to_affine_compatibility;
             iIntros "#Hf";
             by iApply fundamental);
      iIntros "#Hio".
    - by iApply compat_var.
    - iApply compat_lam; fold_interp.
      by iApply "IH".
    - iApply (compat_app _ _ EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight);
        fold_interp.
      + by iApply "IH".
      + by iApply "IH1".
    - iApply (compat_pair _ _ EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight);
        fold_interp.
      + by iApply "IH".
      + by iApply "IH1".
    - iApply (compat_destruct _ _ EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight);
        fold_interp.
      + by iApply "IH".
      + by iApply "IH1".
    - iApply compat_alloc; fold_interp.
      by iApply "IH".
    - iApply (compat_replace _ _ EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight);
        fold_interp.
      + by iApply "IH".
      + by iApply "IH1".
    - iApply compat_dealloc; fold_interp.
      by iApply "IH".
    - by iApply compat_nat.
    - by iApply compat_bool.
    - by iApply compat_unit.
    - iApply (compat_fork _ _ EqDecisionLeft FiniteLeft EqDecisionRight FiniteRight);
        first done; fold_interp.
      + by iApply "IH".
      + by iApply "IH1".
  Qed.

End glue.

Local Definition rs : gReifiers NotCtxDep 3
  := gReifiers_cons reify_fork
       (gReifiers_cons reify_store
          (gReifiers_cons reify_io gReifiers_nil)).

#[local] Parameter Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Open Scope stdpp.

Lemma logrel2_adequacy (cr : nat) Σ R
  `{!Cofe R, !SubOfe natO R, !SubOfe unitO R, !SubOfe locO R}
  `{!invGpreS Σ} `{!statePreG rs R Σ} `{!heapPreG rs R Σ} (τ : ty)
  (α : interp_scope (E := (gReifiers_ops rs)) (R := R) Empty_set -n>
         IT (gReifiers_ops rs) R)
  (β : list.listO (IT (gReifiers_ops rs) R)) st st' k :
  (∀ `{H1 : !gitreeGS_gen rs R Σ} `{H2 : !heapG rs R Σ},
     (⊢@{iProp Σ} @fork_post 3 NotCtxDep rs R _ Σ H1 (RetV ())) →
     (£ cr ⊢ valid2 rs □ α τ)%I) →
  tp_external_steps (gReifiers_sReifier rs) [(α ı_scope)] st β st' k →
  ∀ (e2 : (IT (gReifiers_ops rs) R)), e2 ∈ β →
  is_Some (IT_to_V e2)
  ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) e2 st' β1 st1 l)
  ∨ (∃ e, e2 ≡ Err e ∧ s e).
Proof.
  intros Hlog Hst e2 HIn.
  eapply (wp_tp_progress_gen Σ 3 NotCtxDep rs (S (S (S cr))) (λ x, x) s
            k (α ı_scope) β st st' e2 HIn Hdisj Hst).
  intros H1 H2.
  pose H3 : gitreeGS_gen rs R Σ := AffineLangGitreeGS rs Σ H1 H2.
  simpl in H3.
  exists (λ _, True)%I. split.
  { apply _. }
  iExists (@state_interp_fun _ _ rs _ _ _ H3).
  iExists (@aux_interp_fun _ _ rs _ _ _ H3).
  iExists (@fork_post _ _ rs _ _ _ H3).
  iExists (@fork_post_ne _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_mono _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_ne _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_decomp _ _ rs _ _ _ H3).
  simpl.
  iAssert (True%I) as "G"; first done; iFrame "G"; iClear "G".
  iModIntro. iIntros "((Hone & Hone' & Hone'' & Hcr) & Hst)".
  pose (σ := st.2.1 : gmap.gmapO locO (laterO (IT (gReifiers_ops rs) R))).
  pose (ios := st.2.2.1).
  pose (σfork := st.1).
  iMod (new_heapG rs (to_agree <$> σ)) as (H4) "H".
  iAssert (
      has_substate σfork
      ∗ has_substate
        (σ : oFunctor_car
               (sReifier_state reify_store)
               (IT (sReifier_ops (gReifiers_sReifier rs)) R)
               (IT (sReifier_ops (gReifiers_sReifier rs)) R))
      ∗ has_substate ios)%I with "[Hst]"
    as "[Hsfork [Hs Hio]]".
  { unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) _) st ≡
              of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state σfork)
            ⋅ (of_idx rs (IT (gReifiers_ops rs) _) sR_idx
              (sR_state (σ : oFunctor_car
                    (sReifier_state reify_store)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)))
            ⋅ of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state ios)))%stdpp as ->; last first.
    { rewrite -own_op -own_op -auth_frag_op /=. done. }
    unfold sR_idx. simpl.
    intro j.
    rewrite discrete_fun_lookup_op.
    inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 0%fin)). done. }
    intros j.
    rewrite discrete_fun_lookup_op.
    inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 1%fin)). done. }
    intros j. inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 2%fin)). done. }
    intros i. inversion i.
  }
  iPoseProof (Hlog H3 H4 with "Hcr") as "Hlog".
  { done. }
  iApply fupd_wp.
  iMod (inv_alloc (nroot.@"storeE") _
          (∃ σ : gmap locO (laterO (IT (gReifiers_ops rs) R)),
             £ 1 ∗ has_substate (σ : oFunctor_car
                    (sReifier_state reify_store)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R))
             ∗ own (heapG_name rs) (●V ((to_agree <$> σ) : gmap.gmapO loc (agreeR (laterO (IT (gReifiers_ops rs) R))))))%I
         with "[Hone H Hs]") as "#Hinv".
  {
    iNext. iExists st.2.1.
    iFrame "Hone H Hs".
  }
  iMod (inv_alloc (nroot.@"forkE") _ (£1 ∗ has_substate σfork)%I
         with "[Hone' Hsfork]") as "#Hinv'".
  {
    iNext.
    iFrame "Hone' Hsfork".
  }
  iMod (inv_alloc (nroot.@"ioE") _
          (∃ ios,
             £ 1 ∗ has_substate (ios : oFunctor_car
                    (sReifier_state reify_io)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)))%I
         with "[Hone'' Hio]") as "#Hinv''".
  {
    iNext. iExists _.
    iFrame "Hone'' Hio".
  }
  iSpecialize ("Hlog" with "Hinv''").
  iSpecialize ("Hlog" $! ı_scope with "Hinv []").
  { iApply ssubst_valid_fin_empty1. }
  destruct σfork.
  iSpecialize ("Hlog" with "Hinv'").
  iSpecialize ("Hlog" $! tt with "[//]").
  iModIntro.
  iApply (wp_wand with "Hlog").
  iIntros (βv). simpl. iDestruct 1 as (_) "[H _]".
  done.
Qed.

Definition R := sumO locO (sumO natO unitO).

Lemma logrel2_safety e τ (β : list (IT (gReifiers_ops rs) R)) st st' k :
  typed_glued □ e τ →
  tp_external_steps (gReifiers_sReifier rs) [(interp_expr rs e ı_scope)] st β st' k →
  ∀ e2, e2 ∈ β →
  is_Some (IT_to_V e2)
  ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) e2 st' β1 st1 l)
  ∨ (e2 ≡ Err OtherError).
Proof.
  intros Hty Hst e2 Hin.
  cut (is_Some (IT_to_V e2)
       ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) e2 st' β1 st1 l)
       ∨ (∃ e, e2 ≡ Err e ∧ s e)).
  {
    intros [| [|[err [-> H]]]]; first by left.
    - right. left. done.
    - right. right.
      by rewrite H.
  }
  pose (Σ:=#[invΣ;stateΣ rs R;heapΣ rs R;na_invΣ]).
  eapply (logrel2_adequacy 0 Σ _ τ); eauto.
  iIntros (? ? ?) "_".
  by iApply fundamental_affine_glued.
Qed.
