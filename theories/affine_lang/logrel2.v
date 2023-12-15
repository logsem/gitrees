From Equations Require Import Equations.
From iris.base_logic.lib Require Import na_invariants.
From gitrees Require Export lang_generic gitree program_logic.
From gitrees.input_lang Require Import lang interp logpred.
From gitrees.affine_lang Require Import lang logrel1.
From gitrees.examples Require Import store pairs.
Require Import iris.algebra.gmap.

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

Section glue.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
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

  Context {HCI :
      ∀ o : opid (sReifier_ops (gReifiers_sReifier rs)),
             CtxIndep (gReifiers_sReifier rs) IT o}.

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
  Proof using HCI.
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
      heap_ctx -∗ io_valid empC (constO (glue_from_affine _ ty_conv_unit (α ()))) Tnat.
  Proof.
    iIntros "H #Hctx".
    iIntros (σ ss) "Hs Hss".
    iIntros (_) "Hp".
    simpl. iApply wp_val.
    iModIntro. iExists tt. iFrame. simpl.
    eauto with iFrame.
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
  Proof using HCI.
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
            (pointsto l (Ret 1) ∨
               (pointsto l (Ret 0) ∗ interp_tarr (interp_ty τ1) (interp_ty τ2) αv)) with "[Hl Ha]") as "#Hinv".
    { iNext. iRight. by iFrame. }
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
      iSpecialize ("Hb" $! _ (RetV 0) with "Hs []").
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
  Proof using HCI.
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
    iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Ret n)) with "[Hl']") as "#Hinv".
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
  Proof using HCI.
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
  Proof using HCI.
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

Local Definition rs : gReifiers 2 := gReifiers_cons reify_store (gReifiers_cons input_lang.interp.reify_io gReifiers_nil).

Local Instance CtxIndepInputLang R `{!Cofe R} (o : opid (sReifier_ops (gReifiers_sReifier rs))) :
  CtxIndep (gReifiers_sReifier rs)
    (IT (sReifier_ops (gReifiers_sReifier rs)) R) o.
Proof.
  destruct o as [x o].
  inv_fin x.
  - simpl. intros [[]| [[]| [[] | [| []]]]].
    + constructor.
      unshelve eexists (λne '(l,(σ, σ')), x ← σ !! l;
                        Some (x, (σ, σ'))).
      * apply _.
      * apply _.
      * solve_proper_prepare.
        destruct x as [? [? ?]]; destruct y as [? [? ?]]; simpl in *.
        apply (option_mbind_ne _ (λ n, Some (n, _)) (λ n, Some (n, _))).
        -- intros ? ? ?; repeat f_equiv; [done | |]; apply H.
        -- rewrite lookup_ne; last apply H.
           simpl.
           f_equiv.
           apply H.
      * intros.
        simpl.
        destruct σ as [? [? ?]].
        simpl.
        match goal with
        | |- context G [@mbind option option_bind _ _ ?a ?b] => set (x := b)
        end.
        symmetry.
        match goal with
        | |- context G [@mbind option option_bind _ _ ?a ?b] => set (y := b)
        end.
        assert (y = x) as ->.
        { reflexivity. }
        destruct x as [x |]; reflexivity.
    + constructor.
      unshelve eexists (λne '((l,n),(s, s'')), let s' := <[l:=n]>s
                                               in Some ((), (s', s''))).
      * apply _.
      * solve_proper_prepare.
        destruct x as [[? ?] [? ?]]; destruct y as [[? ?] [? ?]]; simpl in *.
        do 3 f_equiv; last apply H.
        rewrite insert_ne; [| apply H | apply H].
        simpl.
        f_equiv.
        apply H.
      * intros.
        simpl.
        destruct i as [? ?].
        destruct σ as [? [? ?]].
        simpl.
        reflexivity.
    + constructor.
      unshelve eexists (λne '(n,(s, s'')), let l := Loc.fresh (dom s) in
                                      let s' := <[l:=n]>s in
                                      Some (l, (s', s''))).
      * apply _.
      * apply _.
      * solve_proper_prepare.
        destruct x as [? [? ?]]; destruct y as [? [? ?]]; simpl in *.
        do 2 f_equiv.
        -- f_equiv.
           destruct H as [_ [H _]]; simpl in H.
           apply gmap_dom_ne in H.
           apply H.
        -- f_equiv; last apply H.
           rewrite insert_ne; [| apply H | apply H].
           simpl.
           f_equiv.
           destruct H as [_ [H _]]; simpl in H.
           apply gmap_dom_ne in H.
           by rewrite H.
      * intros.
        simpl.
        destruct i as [? ?].
        destruct σ as [? [? ?]].
        simpl.
        reflexivity.
    + constructor.
      simpl.
      unshelve eexists (λne '(l,(σ, σ')), Some ((), (delete l σ, σ'))).
      * apply _.
      * solve_proper_prepare.
        destruct x as [? [? ?]]; destruct y as [? [? ?]]; simpl in *.
        do 2 f_equiv.
        f_equiv; last apply H.
        rewrite delete_ne; last apply H.
        simpl.
        f_equiv.
        apply H.
      * intros.
        simpl.
        destruct σ as [? [? ?]].
        simpl.
        reflexivity.
  - intros x; inv_fin x.
    + simpl. intros [[]| [[]| []]].
      * constructor.
        unshelve eexists (λne '(_, (a, (b, c))), SomeO (_, (_, (_, c)))).
        -- simpl in *.
           apply ((input_lang.lang.update_input b).1).
        -- apply a.
        -- apply ((input_lang.lang.update_input b).2).
        -- solve_proper_prepare.
           destruct x as [? [? [? ?]]]; destruct y as [? [? [? ?]]].
           simpl in *.
           do 2 f_equiv.
           ++ do 2 f_equiv.
              apply H.
           ++ f_equiv; first apply H.
              f_equiv; last apply H.
              do 2 f_equiv; apply H.
        -- intros.
           simpl.
           destruct σ as [? [? ?]].
           simpl.
           reflexivity.
      * constructor.
        unshelve eexists (λne '(x, (y, z)), SomeO ((), _)).
        -- simpl in *.
           apply (y, ((input_lang.lang.update_output x (fstO z)), ())).
        -- solve_proper_prepare.
           destruct x as [? [? [? ?]]]; destruct y as [? [? [? ?]]].
           simpl in *.
           do 2 f_equiv.
           apply pair_ne.
           ++ apply H.
           ++ do 2 f_equiv; apply H.
        -- intros.
           simpl.
           destruct σ as [σ1 [? []]]; simpl in *.
           reflexivity.
    + intros i; by apply fin_0_inv.
Qed.

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logrel2_adequacy cr R `{!Cofe R, !SubOfe locO R, !SubOfe natO R, !SubOfe unitO R} Σ `{!invGpreS Σ}`{!statePreG rs R Σ} `{!heapPreG rs R Σ} `{!na_invG Σ}
  τ (α : unitO -n>  IT (gReifiers_ops rs) R) (β : IT (gReifiers_ops rs) R) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ} p,
      (£ cr ⊢ valid2 rs p empC α τ)%I) →
  ssteps (gReifiers_sReifier rs) (α ()) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (β ≡ Err OtherError)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
      ∨ (∃ e, β ≡ Err e ∧ s e)).
  { intros [?|He]; first eauto. right. left.
    destruct He as [? [? ->]]. done. }
  eapply (wp_safety (S cr) _ _ rs s); eauto.
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
            ⋅ of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state ios)) as ->; last first.
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
  iSpecialize ("Hlog" $! emp_ssubst with "Hinv []").
  { iApply ssubst_valid_nil. }
  unfold expr_pred. simpl.
  iSpecialize ("Hlog" $! ios with "[$Hio $Hp]").
  iModIntro. simp interp_ssubst.
  iApply (wp_wand with "Hlog").
  eauto with iFrame.
Qed.

Definition R := sumO locO (sumO natO unitO).

Lemma logrel2_safety e τ (β : IT (gReifiers_ops rs) R) st st' k :
  typed_glued empC e τ →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ()) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (β ≡ Err OtherError)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs R;heapΣ rs R;na_invΣ]).
  eapply (logrel2_adequacy 0 R Σ); eauto.
  iIntros (? ? ? ?) "_".
  by iApply fundamental_affine_glued.
Qed.
