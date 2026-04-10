(** Unary (Kripke) logical relation for the PRNG lang *)
(** Type safety and adequacy of the GIT interptation *)
From gitrees Require Import gitree program_logic lang_generic.
From gitrees.examples.prng_lang Require Import lang interp prng_seed_combinator.
From gitrees.effects Require Import prng.

Require Import Binding.Lib Binding.Set Binding.Env.

Import IF_nat.

Section prng_logrel.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_prng rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R} `{!SubOfe locO R} `{!SubOfe unitO R} .
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!prngG Σ, !gitreeGS_gen rs R Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).

  (* stuckness and the freely-adjoined kripke frame *)
  Variable s : stuckness.
  Context {A : ofe}.
  Variable (P : A -n> iProp).

  (* expr_pred: gitree value predicate -> gitree predicate *)
  Local Notation expr_pred := (expr_pred s rs P).

  Program Definition val_nat : ITV -n> iProp := λne αv,
    (∃ (n : nat), αv ≡ RetV n)%I.
  Program Definition val_unit : ITV -n> iProp := λne αv,
    (αv ≡ RetV ())%I.
  Program Definition val_prng : ITV -n> iProp := λne αv,
    (∃ (l : loc), αv ≡ RetV l ∗ known_prng l )%I.
  Solve All Obligations with solve_proper.

  Program Definition val_arr (Φ1 Φ2 : ITV -n> iProp) := λne αv,
      (□ ∀ βv, Φ1 βv -∗ expr_pred ((IT_of_V αv) ⊙ (IT_of_V βv)) Φ2)%I.
  Solve All Obligations with solve_proper.

  Fixpoint val_pred (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tunit => val_unit
    | Tnat => val_nat
    | Tprng => val_prng
    | Tarr τ1 τ2 => val_arr (val_pred τ1) (val_pred τ2)
    end.

  (* subst_valid: (S : Names) (Γ : Context S) -> interptation of Γ -> iProp *)
  Notation ssubst_valid := (ssubst_valid1 rs ty val_pred expr_pred).

  #[global] Instance prng_lang_val_pred_persist τ βv : Persistent (val_pred τ βv).
  Proof. induction τ; try apply _. Qed.

  Program Definition valid1 {S : Set} (Γ : S → ty) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    (∀ ss, prng_ctx rs
           -∗ ssubst_valid Γ ss
           -∗ expr_pred (α ss) (λne v, val_pred τ v))%I.
  Solve Obligations with solve_proper.

  Lemma compat_unit {S : Set} (Γ : S → ty) :
    ⊢ valid1 Γ (interp_unit rs) Tunit.
  Proof.
    iIntros (αs) "#Hctx Has".
    by iApply expr_pred_ret.
  Qed.

  Lemma compat_nat {S : Set} (Γ : S → ty) (n : nat) :
    ⊢ valid1 Γ (interp_nat rs n) Tnat.
  Proof.
    iIntros (αs) "#Hctx Has".
    iApply expr_pred_ret.
    by iExists n.
  Qed.

  Lemma compat_var {S : Set} (Γ : S → ty) (v : S) :
    ⊢ valid1 Γ (interp_var v) (Γ v).
  Proof.
    iIntros (ss) "#Hctx Has".
    iIntros (x) "HP".
    iSimpl.
    iSpecialize ("Has" $! v x with "HP").
    iApply (wp_wand with "Has").
    iIntros (v') "HH".
    iDestruct "HH" as "(%y & HH & HP')".
    iModIntro.
    iExists y.
    iFrame.
  Qed.

  Lemma compat_if {S : Set} (Γ : S → ty) τ α β1 β2 :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β1 τ -∗
      valid1 Γ β2 τ -∗
      valid1 Γ (interp_if rs α β1 β2) τ.
  Proof.
    iIntros "H0 H1 H2".
    iIntros (ss) "#Hctx #Has".
    iSpecialize ("H0" with "Hctx Has").
    iApply (expr_pred_bind (IFSCtx _ _) with "H0").
    iIntros (αv) "Ha/=".
    iDestruct "Ha" as (n) "Hn".
    unfold IFSCtx. iIntros (x) "Hx".
    iRewrite "Hn".
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply ("H2" with "Hctx Has Hx").
    - rewrite IF_True; last lia.
      iApply ("H1" with "Hctx Has Hx").
  Qed.


  (* [typed_NewPrng] *)
  Lemma compat_NewPrng {S : Set} {Γ : S → ty} :
    ⊢ valid1 Γ (interp_new rs) Tprng.
  Proof.
    iIntros (ss) "#Hctx #Has".
    iApply expr_pred_frame.
    iApply (wp_new rs Ret s with "Hctx").
    iIntros (l) "!> !> Hprng".
    iApply wp_val.
    iExists l.
    by iFrame.
  Qed.

  (* [typed_DelPrng] has been removed.
     Deleting a potentially shared PRNG state is generally unsafe.
     it is only safe to delete with exclusive ownership.

     Consider the following counterexample program.

     let rng := new_prng in
     let rng_share := rng in
     delete rng; rand rng_share

     We have to make a choice. 
     Either be affine and lose the ability of manual deallocation
     or be linear and restrict sharing.
   *)

  (* [typed_Rand] *)
  Lemma compat_Rand {S : Set} {Γ : S → ty} α :
    ⊢ valid1 Γ α Tprng -∗
      valid1 Γ (interp_rand rs α) Tnat.
  Proof.
    iIntros "H1" (ss) "#Hctx #Has".
    iSpecialize ("H1" $! ss with "Hctx Has").
    iApply (expr_pred_bind (get_ret PRNG_GEN) with "H1").
    iIntros (αv) "(%l & Heq & #Hprng) /=".
    iRewrite "Heq". rewrite IT_of_V_Ret get_ret_ret.
    iApply expr_pred_frame.
    iApply (wp_gen rs l with "Hctx Hprng").
    iIntros "!> !> Hprng' %n".
    by iExists n.
  Qed.

  (* [typed_Seed] *)
  Lemma compat_Seed {S : Set} {Γ : S → ty} α β :
    ⊢ valid1 Γ α Tprng -∗
      valid1 Γ β Tnat -∗
      valid1 Γ (interp_seed rs α β) Tunit.
  Proof.
    iIntros "H1 H2" (ss) "#Hctx #Has". simpl.
    iSpecialize ("H1" $! ss with "Hctx Has").
    iSpecialize ("H2" $! ss with "Hctx Has").
    iApply (expr_pred_bind (SeedGitCtxL rs (β ss)) with "H1").
    iIntros (αv) "(%l & Heq & #Hprng) /=".
    iRewrite "Heq"; rewrite IT_of_V_Ret.
    iApply (expr_pred_bind (SeedGitCtxS rs (Ret l)) with "H2").
    iIntros (βv) "(%sd & Heq)".
    iRewrite "Heq"; rewrite IT_of_V_Ret /SeedGitCtxS SeedGit_Ret.
    iApply expr_pred_frame.
    iApply (wp_seed rs l with "Hctx Hprng").
    iIntros "!> !> Hprng'".
    done.
  Qed.

  Lemma compat_app {S : Set} (Γ : S → ty) α β τ1 τ2 :
    ⊢ valid1 Γ α (Tarr τ1 τ2) -∗
      valid1 Γ β τ1 -∗
      valid1 Γ (interp_app rs α β) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (ss) "#Hctx #Has". simpl.
    iSpecialize ("H2" with "Hctx Has").
    iApply (expr_pred_bind (AppRSCtx _) with "H2").
    iIntros (βv) "Hb/=".
    unfold AppRSCtx.
    iSpecialize ("H1" with "Hctx Has").
    iApply (expr_pred_bind (AppLSCtx (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    unfold AppLSCtx.
    iApply ("Ha" with "Hb").
  Qed.

  Lemma compat_rec {S : Set} (Γ : S → ty) τ1 τ2 α :
    ⊢ □ valid1 (Γ ▹ (Tarr τ1 τ2) ▹ τ1) α τ2 -∗
      valid1 Γ (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (ss) "#Hctx #Hss".
    term_simpl.
    pose (f := (ir_unf rs α ss)).
    iAssert (interp_rec rs α ss ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf". iApply expr_pred_ret. simpl.
    iModIntro.
    iLöb as "IH". iSimpl.
    iIntros (βv) "#Hw".
    iIntros (x) "Hx".
    iApply wp_lam.
    iIntros "!> Hcl".
    pose (ss' := (extend_scope (extend_scope ss (interp_rec rs α ss)) (IT_of_V βv))).
    iSpecialize ("H" $! ss' with "Hctx [Hw]").
    {
      unfold ssubst_valid.
      iIntros ([| [|]]); term_simpl.
      - iModIntro.
        iApply expr_pred_ret.
        iExact "Hw".
      - iModIntro.
        iRewrite "Hf".
        iIntros (x') "Hx".
        iApply wp_val.
        iModIntro.
        iExists x'.
        iFrame "Hx".
        iModIntro.
        iApply "IH".
      - iApply "Hss".
    }
    unfold f.
    by iApply "H".
  Qed.

  Lemma compat_natop {S : Set} (Γ : S → ty) op α β :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β Tnat -∗
      valid1 Γ (interp_natop _ op α β) Tnat.
  Proof.
    iIntros "H1 H2".
    iIntros (ss) "#Hctx #Has". simpl.
    iSpecialize ("H2" with "Hctx Has").
    iApply (expr_pred_bind (NatOpRSCtx _ _) with "H2").
    iIntros (βv) "Hb/=".
    unfold NatOpRSCtx.
    iSpecialize ("H1" with "Hctx Has").
    iApply (expr_pred_bind (NatOpLSCtx _ (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    unfold NatOpLSCtx.
    iDestruct "Hb" as (n1) "Hb".
    iDestruct "Ha" as (n2) "Ha".
    iRewrite "Hb". iRewrite "Ha".
    simpl. iApply expr_pred_frame.
    rewrite NATOP_Ret. iApply wp_val. simpl.
    eauto with iFrame.
  Qed.

  Lemma fundamental {S : Set} (Γ : S → ty) e τ :
    typed Γ e τ → ⊢ valid1 Γ (interp_expr rs e) τ
  with fundamental_val {S : Set} (Γ : S → ty) v τ :
    typed_val Γ v τ → ⊢ valid1 Γ (interp_val rs v) τ.
  Proof.
    - destruct 1.
      + by iApply fundamental_val.
      + subst. by iApply compat_var.
      + iApply compat_app; iApply fundamental; eauto.
      + iApply compat_natop; iApply fundamental; eauto.
      + iApply compat_if;  iApply fundamental; eauto.
      + iApply compat_NewPrng.
        (* + iApply compat_DelPrng; iApply fundamental; eauto. *)
      + iApply compat_Rand; iApply fundamental; eauto.
      + iApply compat_Seed; iApply fundamental; eauto.
    - destruct 1.
      + iApply compat_unit.
      + iApply compat_nat.
      + iApply compat_rec; iApply fundamental; eauto.
  Qed.

  Lemma fundmanetal_closed (e : expr ∅) (τ : ty) :
    typed □ e τ →
    ⊢ valid1 □ (interp_expr rs e) τ.
  Proof. apply fundamental. Qed.

End prng_logrel.

Arguments val_pred {_ _ _ _ _ _ _ _ _ _ _ _ _} τ.
Arguments val_arr {_ _ _ _ _ _ _ _ _} Φ1 Φ2.

(* Closed typed PRNG lang programs are safety to executed.
   We prove this by the safety of GIT interpretation (of typed closed programs) and adequacy
 *)
Section safety_adeqaucy.

Local Definition rs : gReifiers NotCtxDep _ := gReifiers_cons reify_prng gReifiers_nil.

#[local] Parameter Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Program Definition PrngLangGitreeGS {R} `{!Cofe R}
  {a : is_ctx_dep} {n} (rs : gReifiers a n)
  (Σ : gFunctors)
  (H1 : invGS Σ) (H2 : stateG rs R Σ)
  : gitreeGS_gen rs R Σ :=
  GitreeG rs R Σ H1 H2
    (λ _ σ, @state_interp _ _ rs R _ _ H2 σ)
    (λ _, True%I)
    (λ _, True%I)
    _
    (λ x, x)
    _
    _
    _.
Next Obligation.
  intros; simpl.
  iIntros "?". by iModIntro.
Qed.
Next Obligation.
  intros; simpl. iSplit; iIntros "H".
  - by iFrame "H".
  - by iDestruct "H" as "(_ & ?)".
Qed.

(* XXX: need this command to typecheck [β ≡ Err e] *)
Open Scope stdpp.

Lemma logpred_adequacy (cr : nat) Σ R
  `{!Cofe R, !SubOfe natO R, !SubOfe unitO R, !SubOfe locO R}
  `{!invGpreS Σ} `{!statePreG rs R Σ} `{!prngPreG Σ}
  (τ : ty)
  (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R)
  (β : IT (gReifiers_ops rs) R) st st' k :
  (∀ `{H1 : !gitreeGS_gen rs R Σ} `{H2 : !prngG Σ},
      (£ cr ⊢ valid1 rs notStuck (λne _ : unitO, True)%I □ α τ)%I) →
  external_steps (gReifiers_sReifier rs) (α ı_scope) st β st' [] k →
  is_Some (IT_to_V β)
  ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) β st' β1 st1 l)
   ∨ (∃ e : errorO, β ≡ Err e ∧ notStuck e).
Proof.
  intros Hlog Hst.
  eapply (wp_progress_gen Σ 1 NotCtxDep rs (S cr) (λ x, x) notStuck
            [] k (α ı_scope) β st st' Hdisj Hst).
  intros H1 H2.
  pose H3 : gitreeGS_gen rs R Σ := PrngLangGitreeGS rs Σ H1 H2.
  simpl in H3.
  exists (λ _, True)%I. split.
  (*exists (val_pred (s:=notStuck) (P:=(λne _:unitO, True)) τ)%I. split.*)
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
  iModIntro. iIntros "((Hone & Hcr) & Hst)".
  destruct st as [σ []].
  iAssert (has_substate σ) with "[Hst]" as "Hs".
  {
    unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) _) (σ,()) ≡
            of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state σ)) as ->; last done.
    intro j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    {
      inv_fin j; first done.
      intros i. inversion i.
    }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
  }
  iApply fupd_wp.
  iMod (new_prngG σ) as (H4) "Hprng".
  iMod (inv_alloc (nroot.@"prngE") _
          (∃ σ : state,
             £ 1 ∗ has_substate (σ : oFunctor_car
                    (sReifier_state reify_prng)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R)
                    (IT (sReifier_ops (gReifiers_sReifier rs)) R))
                    ∗ has_prngs σ)%I
         with "[Hone Hs Hprng]") as "#Hinv".
  {
    iNext. iExists σ. iFrame.
  }
  iSimpl in "Hinv".
  iPoseProof (Hlog H3 with "Hcr") as "Hlog".
  iSpecialize ("Hlog" $! ı_scope).
  iSpecialize ("Hlog" with "Hinv").
  iAssert (ssubst_valid1 rs ty val_pred
           (expr_pred notStuck rs (λne _ : unitO, True)%I) □ ı_scope) as "Hvalid".
           {
             by iIntros "%Hempty".
           }
  iSpecialize ("Hlog" with "Hvalid").
  iSpecialize ("Hlog" $! () I).
  iApply (wp_wand with "Hlog").
  iModIntro.
  iIntros (βv) "_".
  done.
Qed.

Let R := sumO natO (sumO unitO locO).
Let sRef := gReifiers_sReifier rs.
Let sOps := sReifier_ops sRef.
Let IT := IT sOps R.
Let fullState := sReifier_state sRef ♯ IT.

Lemma prng_lang_safety e τ (st st' : fullState) (β : IT) k :
  typed □ e τ →
  external_steps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) st β st' [] k →
  is_Some (IT_to_V β)
  ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) β st' β1 st1 l).
Proof.
  intros Htyped Hsteps.
  cut (is_Some (IT_to_V β)
       ∨ (∃ β1 st1 l, external_step (gReifiers_sReifier rs) β st' β1 st1 l)
       ∨ (∃ e : errorO, β ≡ Err e ∧ notStuck e)).
  {
    intros [H | [H | [? [? H]]]].
    - by left.
    - by right.
    - done.
  }
  pose (Σ:=#[invΣ;stateΣ rs R;prngΣ]).
  assert (invGpreS Σ) by apply _.
  assert (statePreG rs R Σ) by apply _.
  assert (prngPreG Σ) by apply _.
  eapply (logpred_adequacy 0 Σ); eauto.
  intros ??. iIntros "_".
  by iApply fundamental.
Qed.

End safety_adeqaucy.
Print Assumptions prng_lang_safety.
