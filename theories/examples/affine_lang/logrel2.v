From iris.base_logic.lib Require Import na_invariants.
From gitrees Require Export gitree program_logic greifiers.
From gitrees.examples.input_lang Require Import lang interp logpred.
From gitrees.examples.affine_lang Require Import lang logrel1.
From gitrees.effects Require Import store.
From gitrees.lib Require Import pairs.
From gitrees.utils Require Import finite_sets.

Require Import Binding.Lib Binding.Set Binding.Env.

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
.

Section glue.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).

  Definition s : stuckness := λ e, e = OtherError.
  Variable p : na_inv_pool_name.

  Definition valid2 {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) (α : interp_scope (E:=F) S -n> IT)
    (τ : ty) : iProp :=
     valid1 rs s (λne σ, has_substate σ ∗ na_own p ⊤)%I Ω α τ.

  Definition io_valid {S : Set} (Γ : S → io_lang.ty) α (τ' : io_lang.ty)
    : iProp :=
    input_lang.logpred.valid1 rs s (λne _ : unitO, na_own p ⊤) Γ α τ'.

  Local Opaque thunked thunkedV Thunk.

  Lemma compat_glue_to_affine_bool {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) α :
    io_valid □ α Tnat ⊢
     valid2 Ω (constO (glue2_bool _ (α ı_scope))) tBool.
  Proof.
    iIntros "H".
    iIntros (ss) "#Hctx Has". simpl.
    iIntros (σ) "[Hs Hp]".
    iSpecialize ("H" $! σ ı_scope with "Hs []").
    { iIntros ([]). }
    iSpecialize ("H" $! tt with "Hp").
    simpl.
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

  Lemma compat_glue_to_affine_nat {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) α :
    io_valid □ α Tnat ⊢
      valid2 Ω (constO (α ı_scope)) tInt.
  Proof.
    iIntros "H".
    iIntros (ss) "#Hctx Has". simpl.
    iIntros (σ) "[Hs Hp]".
    iSpecialize ("H" $! σ ı_scope with "Hs []").
    { iIntros ([]). }
    iSpecialize ("H" $! tt with "Hp").
    simpl.
    iApply (wp_wand with "H").
    iIntros (αv). iDestruct 1 as (_) "[Ha Hp]".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iModIntro. eauto with iFrame.
  Qed.

  Lemma compat_glue_from_affine_bool α :
    valid2 □ α tBool ⊢
      heap_ctx rs -∗ io_valid □ α Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (?) "Hp".
    iSpecialize ("H" $! ss with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_fin_empty1. }
    simpl.
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha [Hs Hp]]".
    iModIntro. simpl. iFrame. iExists tt,_; iFrame.
    iDestruct "Ha" as "[Ha|Ha]"; iExists _; eauto.
  Qed.

  Lemma compat_glue_from_affine_nat α :
    valid2 □ α tInt ⊢
      heap_ctx rs -∗ io_valid □ α Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (?) "Hp".
    iSpecialize ("H" $! ss with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_fin_empty1. }
    iApply (wp_wand with "H").
    iIntros (αv) "Ha". iDestruct "Ha" as (σ') "[Ha [Hs Hp]]".
    iModIntro. iExists tt. eauto with iFrame.
  Qed.

  Lemma compat_glue_from_affine_unit α :
    valid2 □ α tUnit ⊢
      heap_ctx rs -∗ io_valid □ (constO (glue_from_affine _ ty_conv_unit (α ı_scope))) Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (?) "Hp".
    simpl. iApply wp_val.
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
    iIntros "H #Hctx".
    unfold io_valid.
    unfold logpred.valid1.
    iIntros (σ ss) "Hs ?".
    simpl.
    iIntros (?) "Hp".
    iSpecialize ("H" $! ss with "Hctx [] [$Hs $Hp]").
    { iApply ssubst_valid_fin_empty1. }
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
            (pointsto l (Ret 1) ∨
               (pointsto l (Ret 0) ∗ interp_tarr (interp_ty τ1) (interp_ty τ2) αv)) with "[Hl Ha]") as "#Hinv".
    { iNext. iRight. by iFrame. }
    iModIntro. simpl. iApply wp_val.
    iModIntro. iExists tt. iFrame. iExists σ'. iFrame.
    iModIntro. clear σ σ'. iIntros (σ βv) "Hs #Hb".
    iIntros (?) "Hp".
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
      iSpecialize ("Hb" $! _ (RetV 0) with "Hs []").
      { eauto with iFrame. }
      iSpecialize ("Hb" $! tt with "Hp").
      iApply (wp_wand with "Hb").
      iIntros (γv). iDestruct 1 as (?) "[Hg Hp]".
      iDestruct "Hg" as (σ') "[Hg Hst]".
      iModIntro. simpl.
      iApply wp_let.
      { solve_proper. }
      iPoseProof (G1 (constO (IT_of_V γv))) as "G1".
      iSpecialize ("G1" with "[Hg]").
      { iIntros (σ0 ss0) "Hs Has". simpl.
        iApply expr_pred_ret. simpl. eauto with iFrame. }
      iSpecialize ("G1" $! ss with "Hctx [] [$Hst $Hp]").
      { iApply ssubst_valid_fin_empty1. }
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
      iSpecialize ("G1" $! _ ı_scope with  "Hst []").
      {
        iIntros ([]).
      }
      iApply ("G1" $! tt with "Hp").
  Qed.

  Lemma compat_glue_to_affine_fun {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) (τ1 τ2 : ty)
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
    iIntros (αs) "#Hctx Has".
    iIntros (σ) "[Hs Hp]". simpl.
    iSpecialize ("H" $! _ ı_scope with "Hs []").
    { iIntros ([]). }
    iSpecialize ("H" $! tt with "Hp").
    simpl.
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
    iSpecialize ("G2" $! _ ı_scope with "Hs []").
    {
      iIntros ([]).
    }
    iSpecialize ("G2" $! tt with "Hp").
    iApply (wp_wand with "G2").
    iIntros (β'v).
    iDestruct 1 as (?) "[Hb Hp]". iModIntro.
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
    iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Ret n)) with "[Hl']") as "#Hinv".
    { iNext. iExists _; done. }
    iPoseProof ("Ha" $! _ (thunkedV (IT_of_V β'v) l') with "Hs [-Has Hp]") as "H1".
    { iModIntro. iIntros (σ' βn) "Hs Hbm".
      iDestruct "Hbm" as (m) "Hbm".
      iIntros (?) "Hp".
      iApply wp_lam. iNext. iSimpl.
      iApply (wp_bind _ (IFSCtx _ _)).
      { solve_proper. }
      iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
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
        iApply wp_seq.
        { solve_proper. }
        iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
        { set_solver. }
        iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
        iModIntro. iExists (Ret n). iFrame.
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
    iIntros (γv). iDestruct 1 as (?) "[H2 Hp]".
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

  Lemma glue_to_affine_compatibility {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') α :
    io_valid □ α τ1' ⊢ valid2 Ω (constO (glue_to_affine _ Hconv (α ı_scope))) τ1
  with glue_from_affine_compatibility (τ1 : ty) (τ1' : io_lang.ty)
    (Hconv : ty_conv τ1 τ1') (α : IT) :
    valid2 □ (constO α) τ1 ⊢ heap_ctx rs -∗ io_valid □ (constO (glue_from_affine _ Hconv α)) τ1'.
  Proof.
    - destruct Hconv.
      + by iApply compat_glue_to_affine_bool.
      + by iApply compat_glue_to_affine_nat.
      + iIntros "_".
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

  Lemma fundamental_affine_glued {S : Set} `{HE : EqDecision S} `{!Finite S} (Ω : S → ty) (e : expr S) τ :
    typed_glued Ω e τ →
    ⊢ valid2 Ω (interp_expr _ e) τ.
  Proof.
    intros typed.
    iStartProof.
    iInduction typed as [| | | | | | | | | | |] "IH".
    - iApply glue_to_affine_compatibility.
      by iApply fundamental.
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

End glue.

Local Definition rs : gReifiers NotCtxDep 2
  := gReifiers_cons reify_store
       (gReifiers_cons reify_io gReifiers_nil).

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logrel2_adequacy (cr : nat) R `{!Cofe R, !SubOfe locO R, !SubOfe natO R, !SubOfe unitO R}
  Σ `{!invGpreS Σ}`{!statePreG rs R Σ} `{!heapPreG rs R Σ} `{!na_invG Σ}
  (τ : ty) (α : interp_scope Empty_set -n> IT (gReifiers_ops rs) R) (β : IT (gReifiers_ops rs) R) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ} p,
      (£ cr ⊢ valid2 rs p □ α τ)%I) →
  ssteps (gReifiers_sReifier rs) (α ı_scope) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (β ≡ Err OtherError)%stdpp
   ∨ (∃ βv, (IT_of_V βv ≡ β)%stdpp).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
      ∨ (∃ e, (β ≡ Err e)%stdpp ∧ s e)).
  { intros [?|He]; first eauto. right. left.
    destruct He as [? [? ->]]. done. }
  eapply (wp_safety (S cr) _ _ NotCtxDep rs s); eauto.
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
  iMod (inv_alloc (nroot.@"storeE") _ (∃ σ, £ 1 ∗ has_substate σ ∗ own (heapG_name rs) (●V σ))%I with "[-Hcr Hio]") as "#Hinv".
  { iNext. iExists _. iFrame. }
  simpl.
  iMod na_alloc as (p) "Hp".
  iPoseProof (@Hlog _ _ _ p with "Hcr") as "Hlog".
  iSpecialize ("Hlog" $! ı_scope with "Hinv []").
  { iApply ssubst_valid_fin_empty1. }
  unfold expr_pred. simpl.
  iSpecialize ("Hlog" $! ios with "[$Hio $Hp]").
  iModIntro. simpl.
  iApply (wp_wand with "Hlog").
  eauto with iFrame.
Qed.

Definition R := sumO locO (sumO natO unitO).

Lemma logrel2_safety e τ (β : IT (gReifiers_ops rs) R) st st' k :
  typed_glued □ e τ →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (β ≡ Err OtherError)%stdpp
   ∨ (∃ βv, (IT_of_V βv ≡ β)%stdpp).
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs R;heapΣ rs R;na_invΣ]).
  eapply (logrel2_adequacy 0 R Σ); eauto.
  iIntros (? ? ? ?) "_".
  by iApply fundamental_affine_glued.
Qed.
