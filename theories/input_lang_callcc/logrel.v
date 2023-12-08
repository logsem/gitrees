(** Logical relation for adequacy for the IO lang *)
From Equations Require Import Equations.
From gitrees Require Import gitree.
From gitrees.input_lang_callcc Require Import lang interp.
Require Import gitrees.lang_generic_sem.
Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope stdpp_scope.
Open Scope syn_scope.

Section logrel.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F natO).
  Notation ITV := (ITV F natO).
  Context `{!invGS Σ, !stateG rs natO Σ}.
  Notation iProp := (iProp Σ).
  Notation restO := (gState_rest sR_idx rs ♯ IT).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).
  Canonical Structure ectxO S := leibnizO (ectx S).

  Class LogRelNotation (A : Set -> Type) (B : Type) (C : Set -> Type) := { __logrel : ∀ (S : Set), (A S) -> B -> (C S) -> iProp }.

  Notation "T '@' a '≺' b" := (__logrel _ T a b) (at level 98) : bi_scope.

  Notation "⟦ e ⟧ₑ ρ" := (interp_expr rs e ρ) (at level 200).
  Notation "⟦ v ⟧ᵥ ρ" := (interp_val rs v ρ) (at level 200).
  Notation "⟦ K ⟧ₖ  ρ" := (interp_ectx rs K ρ) (at level 200).
  Notation "⟦ S ⟧ᵨ" := (@interp_scope F natO _ S) (at level 200).

  Notation "'WP' α {{ β , Φ } }" := (wp rs α notStuck ⊤ (λ β, Φ))
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  β ,  Φ  } }") : bi_scope.

  Notation "'WP' α {{ Φ } }" := (wp rs α notStuck ⊤ Φ)
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  Φ  } }") : bi_scope.

  Definition logrel_nat {S} (βv : ITV) (v : val S) : iProp :=
    (∃ n, βv ≡ RetV n ∧ ⌜v = LitV n⌝)%I.

  Definition obs_ref {S} (α : IT) (e : expr S) : iProp :=
    (∀ (σ : stateO),
        has_substate σ -∗
        WP α {{ βv, ∃ m v σ', ⌜prim_steps e σ (Val v) σ' m⌝
                              ∗ logrel_nat βv v ∗ has_substate σ' }})%I.

  Notation "α ↓ e" := (obs_ref α e) (at level 100) : bi_scope.

  Definition HOM : ofe := @sigO (IT -n> IT) IT_hom.

  Global Instance HOM_hom (κ : HOM) : IT_hom (`κ).
  Proof.
    apply (proj2_sig κ).
  Qed.

  Definition logrel_ectx {S} V (κ : HOM) (K : ectx S) : iProp :=
    (□ ∀ (βv : ITV) (v : val S), V βv v -∗ (`κ (IT_of_V βv)) ↓ (K ⟪ Val v ⟫))%I.

  Instance LogRelNotationECtx : LogRelNotation (fun S => ITV → val S → iPropI Σ) HOM ectx := {
      __logrel S V κ K := logrel_ectx V κ K
    }.

  Lemma HOM_ccompose (f g : HOM)
    : ∀ α, `f (`g α) = (`f ◎ `g) α.
  Proof.
    intro; reflexivity.
  Qed.

  Program Definition HOM_compose (f g : HOM) : HOM := exist _ (`f ◎ `g) _.
  Next Obligation.
    intros f g; simpl.
    apply _.
  Qed.

  Program Definition id_HOM : HOM := exist _ idfun _.
  Next Obligation.
    apply _.
  Qed.

  Program Definition AppRSCtx_HOM {S : Set}
    (α : ⟦ S ⟧ᵨ -n> IT)
    (env : ⟦ S ⟧ᵨ)
    : HOM := exist _ (interp_apprk rs α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition AppLSCtx_HOM {S : Set}
    (β : IT) (env : ⟦ S ⟧ᵨ)
    (Hv : AsVal β)
    : HOM := exist _ (interp_applk rs (λne env, idfun) (constO β) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition OutputSCtx_HOM {S : Set}
    (env : ⟦ S ⟧ᵨ)
    : HOM := exist _ (interp_outputk rs (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition ThrowLSCtx_HOM {S : Set}
    (α : ⟦ S ⟧ᵨ -n> IT)
    (env : ⟦ S ⟧ᵨ)
    : HOM := exist _ (interp_throwlk rs (λne env, idfun) α env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition ThrowRSCtx_HOM {S : Set}
    (β : IT) (env : ⟦ S ⟧ᵨ)
    (Hv : AsVal β)
    : HOM := exist _ (interp_throwrk rs (constO β) (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - solve_proper_prepare.
      destruct Hv as [? <-].
      rewrite ->2 get_val_ITV.
      simpl.
      by f_equiv.
    - destruct Hv as [? <-].
      rewrite ->2 get_val_ITV.
      simpl.
      rewrite get_fun_tick.
      f_equiv.
    - destruct Hv as [x Hv].
      rewrite <- Hv.
      rewrite -> get_val_ITV.
      simpl.
      rewrite get_fun_vis.
      repeat f_equiv.
      intro; simpl.
      rewrite <- Hv.
      rewrite -> get_val_ITV.
      simpl.
      f_equiv.
    - destruct Hv as [? <-].
      rewrite get_val_ITV.
      simpl.
      rewrite get_fun_err.
      reflexivity.
  Qed.

  Program Definition NatOpRSCtx_HOM {S : Set} (op : nat_op)
    (α : ⟦ S ⟧ᵨ -n> IT) (env : ⟦ S ⟧ᵨ)
    : HOM := exist _ (interp_natoprk rs op α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition NatOpLSCtx_HOM {S : Set} (op : nat_op)
    (α : IT) (env : ⟦ S ⟧ᵨ)
    (Hv : AsVal α)
    : HOM := exist _ (interp_natoplk rs op (λne env, idfun) (constO α) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition IFSCtx_HOM α β : HOM := exist _ (λne x, IFSCtx α β x) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Definition logrel_expr {S} V (α : IT) (e : expr S) : iProp :=
    (∀ (κ : HOM) (K : ectx S),
       V @ κ ≺ K -∗ (`κ α) ↓ (K ⟪ e ⟫))%I.

  Class AsSemExpr (F : Type) := { __asSemExpr : F -> IT }.

  Arguments __asSemExpr {_} {_}.

  Global Instance AsSemExprIT : AsSemExpr IT := {
      __asSemExpr e := e
    }.
  Global Instance AsSemExprITV : AsSemExpr ITV := {
      __asSemExpr v := IT_of_V v
    }.

  Instance LogRelNotationExpr {F : Set -> Type} {G : Type} `{AsSynExpr F} `{AsSemExpr G} : LogRelNotation (fun S => ITV → val S → iPropI Σ) G F := {
      __logrel S V α e := logrel_expr V (__asSemExpr α) (__asSynExpr e)
    }.

  Definition logrel_arr {S} V1 V2 (βv : ITV) (vf : val S) : iProp :=
    (∃ f, IT_of_V βv ≡ Fun f ∧ □ ∀ αv v, V1 αv v -∗
      V2 @ APP' (Fun f) (IT_of_V αv) ≺ App (Val vf) (Val v))%I.

  Global Instance denot_cont_ne (κ : IT -n> IT) :
    NonExpansive (λ x : IT, Tau (laterO_map κ (Next x))).
  Proof.
    solve_proper.
  Qed.

  Definition logrel_cont {S} V (βv : ITV) (v : val S) : iProp :=
    (∃ (κ : HOM) K, (IT_of_V βv) ≡ (Fun (Next (λne x, Tau (laterO_map (`κ) (Next x)))))
                            ∧ ⌜v = ContV K⌝
                            ∧ □ (V @ κ ≺ K))%I.

  Fixpoint logrel_val {S} (τ : ty) : ITV → (val S) → iProp
    := match τ with
       | Tnat => logrel_nat
       | Tarr τ1 τ2 => logrel_arr (logrel_val τ1) (logrel_val τ2)
       | Tcont τ => logrel_cont (logrel_val τ)
       end.

  Notation "⟦ τ ⟧ₜ" := (logrel_val τ) (at level 200).

  Definition logrel {S} (τ : ty) : IT → (expr S) → iProp
    := logrel_expr (logrel_val τ).

  #[export] Instance obs_ref_ne {S} :
    NonExpansive2 (@obs_ref S).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_expr_ne {S} (V : ITV → val S → iProp) :
    NonExpansive2 V → NonExpansive2 (logrel_expr V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_nat_ne {S} : NonExpansive2 (@logrel_nat S).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_val_ne {S} (τ : ty) : NonExpansive2 (@logrel_val S τ).
  Proof.
    induction τ; simpl; solve_proper.
  Qed.

  #[export] Instance logrel_ectx_ne {S} (V : ITV → val S → iProp) :
    NonExpansive2 V → NonExpansive2 (logrel_ectx V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_arr_ne {S} (V1 V2 : ITV → val S → iProp) :
    NonExpansive2 V1 -> NonExpansive2 V2 → NonExpansive2 (logrel_arr V1 V2).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_cont_ne {S} (V : ITV → val S → iProp) :
    NonExpansive2 V -> NonExpansive2 (logrel_cont V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance obs_ref_proper {S} :
    Proper ((≡) ==> (≡) ==> (≡)) (@obs_ref S).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_expr_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V → Proper ((≡) ==> (≡) ==> (≡)) (logrel_expr V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_nat_proper {S} : Proper ((≡) ==> (≡) ==> (≡)) (@logrel_nat S).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_val_proper {S} (τ : ty) : Proper ((≡) ==> (≡) ==> (≡)) (@logrel_val S τ).
  Proof.
    induction τ; simpl; solve_proper.
  Qed.

  #[export] Instance logrel_ectx_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V → Proper ((≡) ==> (≡) ==> (≡)) (logrel_ectx V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_arr_proper {S} (V1 V2 : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V1 -> Proper ((≡) ==> (≡) ==> (≡)) V2 → Proper ((≡) ==> (≡) ==> (≡)) (logrel_arr V1 V2).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_cont_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V -> Proper ((≡) ==> (≡) ==> (≡)) (logrel_cont V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_val_persistent {S} (τ : ty) α v :
    Persistent (@logrel_val S τ α v).
  Proof.
    revert α v. induction τ=> α v; simpl.
    - unfold logrel_nat. apply _.
    - unfold logrel_arr. apply _.
    - unfold logrel_cont. apply _.
  Qed.

  #[export] Instance logrel_ectx_persistent {S} V κ K :
    Persistent (@logrel_ectx S V κ K).
  Proof.
    apply _.
  Qed.

  Lemma logrel_of_val {S} τ αv (v : val S) :
    (⟦ τ ⟧ₜ) αv v -∗ logrel τ (IT_of_V αv) (Val v).
  Proof.
    iIntros "H1".
    iIntros (κ K) "HK".
    iIntros (σ) "Hs".
    by iApply ("HK" $! αv v with "[$H1] [$Hs]").
  Qed.

  Lemma logrel_head_step_pure_ectx {S} n K (κ : HOM) (e' e : expr S) α V :
    (∀ σ K, head_step e σ e' σ K (n, 0)) →
    ⊢ V @ (`κ α) ≺ (K ⟪ e' ⟫) -∗ V @ (`κ α) ≺ (K ⟪ e ⟫).
  Proof.
    intros Hpure.
    iIntros "H".
    iIntros (κ' K') "#HK'".
    iIntros (σ) "Hs".
    iSpecialize ("H" with "HK'").
    iSpecialize ("H" with "Hs").
    iApply (wp_wand with "H").
    iIntros (βv). iDestruct 1 as ([m m'] v σ' Hsteps) "[H2 Hs]".
    iExists ((Nat.add n m),m'),v,σ'. iFrame "H2 Hs".
    iPureIntro.
    eapply (prim_steps_app (n, 0) (m, m')); eauto.
    eapply prim_step_steps.
    rewrite !fill_comp.
    eapply Ectx_step; last apply Hpure; done.
  Qed.

  Lemma obs_ref_bind {S} (f : HOM) (K : ectx S)
    (e : expr S) α τ1 :
    ⊢ logrel τ1 α e -∗
      logrel_ectx (logrel_val τ1) f K -∗
      obs_ref (`f α) (fill K e).
  Proof.
    iIntros "H1 #H2".
    iIntros (σ) "Hs".
    iApply (wp_wand with "[H1 H2 Hs] []"); first iApply ("H1" with "[H2] [$Hs]").
    - iIntros (βv v). iModIntro.
      iIntros "#Hv".
      by iApply "H2".
    - iIntros (βv).
      iIntros "?".
      iModIntro.
      iFrame.
  Qed.

  Definition ssubst2_valid {S : Set}
    (Γ : S -> ty)
    (ss : ⟦ S ⟧ᵨ)
    (γ : S [⇒] Empty_set)
    : iProp :=
    (∀ x, □ logrel (Γ x) (ss x) (γ x))%I.

  Definition logrel_valid {S : Set}
    (Γ : S -> ty)
    (e : expr S)
    (α : ⟦ S ⟧ᵨ -n> IT)
    (τ : ty) : iProp :=
    (□ ∀ (ss : ⟦ S ⟧ᵨ)
       (γ : S [⇒] Empty_set),
       ssubst2_valid Γ ss γ → logrel τ (α ss) (bind γ e))%I.

  Lemma compat_var {S : Set} (Γ : S -> ty) (x : S) :
    ⊢ logrel_valid Γ (Var x) (interp_var x) (Γ x).
  Proof.
    iModIntro.
    iIntros (ss γ) "Hss".
    iApply "Hss".
  Qed.

  Lemma compat_recV {S : Set} (Γ : S -> ty) (e : expr (inc (inc S))) τ1 τ2 α :
    ⊢ □ logrel_valid ((Γ ▹ (Tarr τ1 τ2) ▹ τ1)) e α τ2 -∗
      logrel_valid Γ (Val $ RecV e) (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (ss γ) "#Hss".
    pose (env := ss). fold env.
    pose (f := (ir_unf rs α env)).
    iAssert (interp_rec rs α env ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf".
    Opaque IT_of_V.
    iApply logrel_of_val; term_simpl.
    iExists _. simpl.
    iSplit.
    { Transparent IT_of_V. done. }
    iModIntro.
    iLöb as "IH". iSimpl.
    iIntros (αv v) "#Hw".
    rewrite APP_APP'_ITV.
    rewrite APP_Fun.
    rewrite laterO_map_Next.
    rewrite -Tick_eq.
    iIntros (κ K) "#HK".
    iIntros (σ) "Hs".
    rewrite hom_tick.
    iApply wp_tick.
    iNext.
    unfold f.
    Opaque extend_scope.
    Opaque IT_of_V.
    simpl.
    pose (ss' := (extend_scope (extend_scope env (interp_rec rs α env)) (IT_of_V αv))).
    pose (γ' := ((mk_subst (Val (rec bind ((γ ↑) ↑)%bind e)%syn)) ∘ ((mk_subst (shift (Val v))) ∘ ((γ ↑) ↑)%bind))%bind : inc (inc S) [⇒] Empty_set).
    iSpecialize ("H" $! ss' γ' with "[]"); last first.
    - iSpecialize ("H" $! κ K with "HK").
      unfold ss'.
      iSpecialize ("H" $! σ with "Hs").
      iApply (wp_wand with "[$H] []").
      iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H)".
      destruct m as [m m'].
      iModIntro.
      iExists ((Nat.add 1 m), m'), v'', σ''. iFrame "H".
      iPureIntro.
      eapply (prim_steps_app (1, 0) (m, m')); eauto.
      term_simpl.
      eapply prim_step_steps.
      eapply Ectx_step; [reflexivity | reflexivity |].
      subst γ'.
      rewrite -!bind_bind_comp'.
      econstructor.
    - Transparent extend_scope.
      iIntros (x'); destruct x' as [| [| x']].
      + term_simpl.
        iModIntro.
        by iApply logrel_of_val.
      + term_simpl.
        iModIntro.
        iRewrite "Hf".
        iIntros (κ' K') "#HK'".
        iApply "HK'".
        simpl.
        unfold logrel_arr.
        _iExists (Next (ir_unf rs α env)).
        iSplit; first done.
        iModIntro.
        iApply "IH".
      + iModIntro.
        subst γ'.
        term_simpl.
        iApply "Hss".
  Qed.

  Lemma compat_if {S : Set} (Γ : S -> ty) (e0 e1 e2 : expr S) α0 α1 α2 τ :
    ⊢ logrel_valid Γ e0 α0  Tnat -∗
      logrel_valid Γ e1 α1 τ -∗
      logrel_valid Γ e2 α2 τ -∗
      logrel_valid Γ (If e0 e1 e2) (interp_if rs α0 α1 α2) τ.
  Proof.
    iIntros "#H0 #H1 #H2".
    iModIntro.
    iIntros (ss γ) "#Hss".
    iEval (term_simpl).
    pose (κ' := (IFSCtx_HOM (α1 ss) (α2 ss))).
    assert ((IF (α0 ss) (α1 ss) (α2 ss)) = ((`κ') (α0 ss))) as ->.
    { reflexivity. }
    iIntros (κ K) "#HK".
    assert ((`κ) ((`κ') (α0 ss)) = ((`κ) ◎ (`κ')) (α0 ss)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }
    assert (fill K (If (bind γ e0) (bind γ e1) (bind γ e2))%syn = fill (ectx_compose K (IfK EmptyK (bind γ e1) (bind γ e2))) (bind γ e0)) as ->.
    {
      rewrite -fill_comp.
      reflexivity.
    }
    iApply (obs_ref_bind with "[H0] [H1 H2]").
    - by iApply "H0".
    - iIntros (βv v). iModIntro. iIntros "#HV".
      term_simpl.
      unfold logrel_nat.
      iDestruct "HV" as "(%n & #Hn & ->)".
      iRewrite "Hn".
      destruct (decide (0 < n)).
      + rewrite -fill_comp.
        simpl.
        unfold IFSCtx.
        rewrite IF_True//.
        iSpecialize ("H1" with "Hss").
        term_simpl.
        iSpecialize ("H1" $! κ K with "HK").
        iIntros (σ) "Hσ".
        iSpecialize ("H1" $! σ with "Hσ").
        iApply (wp_wand with "[$H1] []").
        iIntros (v) "(%m & %w & %σ' & %Hstep & H & G)".
        iModIntro.
        destruct m as [m m'].
        iExists (m, m'), w, σ'. iFrame "H G".
        iPureIntro.
        eapply (prim_steps_app (0, 0) (m, m')); eauto.
        eapply prim_step_steps.
        eapply Ectx_step; [reflexivity | reflexivity |].
        apply IfTrueS; done.
      + rewrite -fill_comp.
        simpl.
        unfold IFSCtx.
        rewrite IF_False//; last lia.
        iSpecialize ("H2" with "Hss").
        term_simpl.
        iSpecialize ("H2" $! κ K with "HK").
        iIntros (σ) "Hσ".
        iSpecialize ("H2" $! σ with "Hσ").
        iApply (wp_wand with "[$H2] []").
        iIntros (v) "(%m & %w & %σ' & %Hstep & H & G)".
        iModIntro.
        destruct m as [m m'].
        iExists (m, m'), w, σ'. iFrame "H G".
        iPureIntro.
        eapply (prim_steps_app (0, 0) (m, m')); eauto.
        eapply prim_step_steps.
        eapply Ectx_step; [reflexivity | reflexivity |].
        apply IfFalseS.
        lia.
  Qed.

  Lemma compat_input {S} Γ :
    ⊢ logrel_valid Γ (Input : expr S) (interp_input rs) Tnat.
  Proof.
    iModIntro.
    iIntros (ss γ) "#Hss".
    iIntros (κ K) "#HK".
    unfold interp_input.
    term_simpl.
    iIntros (σ) "Hs".
    destruct (update_input σ) as [n σ'] eqn:Hinp.
    rewrite hom_vis.
    iApply (wp_subreify with "Hs").
    - simpl; rewrite Hinp.
      rewrite later_map_Next.
      rewrite ofe_iso_21.
      reflexivity.
    - reflexivity.
    - iNext.
      iIntros "Hlc Hs".
      iSpecialize ("HK" $! (RetV n) (LitV n) with "[]"); first by iExists n.
      iSpecialize ("HK" $! σ' with "Hs").
      iApply (wp_wand with "[$HK] []").
      iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H)".
      destruct m as [m m'].
      iModIntro.
      iExists ((Nat.add 1 m), (Nat.add 1 m')), v'', σ''. iFrame "H".
      iPureIntro.
      eapply (prim_steps_app (1, 1) (m, m')); eauto.
      term_simpl.
      eapply prim_step_steps.
      eapply Ectx_step; [reflexivity | reflexivity |].
      constructor.
      assumption.
  Qed.

  Lemma compat_natop {S : Set} (Γ : S -> ty) e1 e2 α1 α2 op :
    ⊢ logrel_valid Γ e1 α1 Tnat -∗
      logrel_valid Γ e2 α2 Tnat -∗
      logrel_valid Γ (NatOp op e1 e2) (interp_natop rs op α1 α2) Tnat.
  Proof.
    iIntros "#H1 #H2".  iIntros (ss γ). iModIntro. iIntros "#Hss".
    iSpecialize ("H1" with "Hss").
    iSpecialize ("H2" with "Hss").
    term_simpl.
    pose (κ' := (NatOpRSCtx_HOM op α1 ss)).
    assert ((NATOP (do_natop op) (α1 ss) (α2 ss)) = ((`κ') (α2 ss))) as ->.
    { reflexivity. }
    iIntros (κ K) "#HK".
    assert ((`κ) ((`κ') (α2 ss)) = ((`κ) ◎ (`κ')) (α2 ss)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }
    assert (fill K (NatOp op (bind γ e1) (bind γ e2))%syn = fill (ectx_compose K (NatOpRK op (bind γ e1) EmptyK)) (bind γ e2)) as ->.
    { rewrite -fill_comp.
      reflexivity.
    }
    iApply (obs_ref_bind with "[H1] [H2]").
    - by iApply "H2".
    - iIntros (βv v). iModIntro. iIntros "(%n1 & #HV & ->)".
      term_simpl.
      subst κ' sss.
      unfold NatOpLSCtx.
      rewrite -fill_comp.
      simpl.
      pose (κ' := (NatOpLSCtx_HOM op (IT_of_V βv) ss _)).
      assert ((NATOP (do_natop op) (α1 ss) (IT_of_V βv)) = ((`κ') (α1 ss))) as ->.
      { reflexivity. }
      assert ((`κ) ((`κ') (α1 ss)) = ((`κ) ◎ (`κ')) (α1 ss)) as ->.
      { reflexivity. }
      pose (sss := (HOM_compose κ κ')).
      assert ((`κ ◎ `κ') = (`sss)) as ->.
      { reflexivity. }
      assert (fill K (NatOp op (bind γ e1) (LitV n1))%syn = fill (ectx_compose K (NatOpLK op EmptyK (LitV n1))) (bind γ e1)) as ->.
      { rewrite -fill_comp.
        reflexivity.
      }
      iApply (obs_ref_bind with "[H1] [H2]").
      + by iApply "H1".
      + subst sss κ'.
        term_simpl.
        iIntros (t r). iModIntro. iIntros "(%n2 & #H & ->)".
        simpl.
        iAssert ((NATOP (do_natop op) (IT_of_V t) (IT_of_V βv)) ≡ Ret (do_natop op n2 n1))%I with "[HV H]" as "Hr".
        { iRewrite "HV". simpl.
          iRewrite "H". simpl.
          iPureIntro.
          by rewrite NATOP_Ret.
        }
        iRewrite "Hr".
        rewrite -fill_comp.
        simpl.
        rewrite -IT_of_V_Ret.
        iSpecialize ("HK" $! (RetV (do_natop op n2 n1)) (LitV (do_natop op n2 n1)) with "[]").
        {
          unfold logrel_nat.
          by iExists (do_natop op n2 n1).
        }
        iIntros (σ) "Hs".
        iSpecialize ("HK" $! σ with "Hs").
        iApply (wp_wand with "[$HK] []").
        simpl.
        iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H' & G)".
        destruct m as [m m'].
        iModIntro.
        iExists (m, m'), v'', σ''. iFrame "H' G".
        iPureIntro.
        eapply (prim_steps_app (0, 0) (m, m')); eauto.
        term_simpl.
        eapply prim_step_steps.
        eapply Ectx_step; [reflexivity | reflexivity |].
        constructor.
        simpl.
        reflexivity.
  Qed.

  Lemma compat_throw {S : Set} (Γ : S -> ty) τ τ' α β e e' :
    ⊢ logrel_valid Γ e α τ -∗
      logrel_valid Γ e' β (Tcont τ) -∗
      logrel_valid Γ (Throw e e') (interp_throw _ α β) τ'.
  Proof.
    iIntros "#H1 #H2".
    iIntros (ss γ). iModIntro. iIntros "#Hss".
    iIntros (κ K) "#HK".
    Opaque interp_throw.
    term_simpl.
    pose (κ' := ThrowLSCtx_HOM β ss).
    assert ((interp_throw rs α β ss) = ((`κ') (α ss))) as ->.
    { reflexivity. }
    assert ((`κ) ((`κ') (α ss)) = ((`κ) ◎ (`κ')) (α ss)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }
    assert (fill K (Throw (bind γ e) (bind γ e'))%syn = fill (ectx_compose K (ThrowLK  EmptyK (bind γ e'))) (bind γ e)) as ->.
    { rewrite -fill_comp.
      reflexivity.
    }
    iApply obs_ref_bind; first by iApply "H1".
    iIntros (βv v). iModIntro. iIntros "#Hv".
    Transparent interp_throw.
    simpl.
    rewrite get_val_ITV'.
    simpl.
    rewrite -!fill_comp.
    simpl.
    pose (κ'' := @ThrowRSCtx_HOM S (IT_of_V βv) ss _).
    (* TODO: some typeclasses bs *)
    assert ((get_fun (λne f : laterO (IT -n> IT), THROW (IT_of_V βv) f) (β ss)) ≡
              ((`κ'') (β ss))) as ->.
    {
      subst κ''. simpl. by rewrite get_val_ITV.
    }
    assert ((`κ) ((`κ'') (β ss)) = ((`κ) ◎ (`κ'')) (β ss)) as ->.
    { reflexivity. }
    pose (sss' := (HOM_compose κ κ'')).
    assert ((`κ ◎ `κ'') = (`sss')) as ->.
    { reflexivity. }
    assert (fill K (Throw v (bind γ e'))%syn = fill (ectx_compose K (ThrowRK v EmptyK)) (bind γ e')) as ->.
    { rewrite -fill_comp.
      reflexivity.
    }
    iApply obs_ref_bind; first by iApply "H2".
    iIntros (βv' v'). iModIntro. iIntros "#Hv'".
    Transparent interp_throw.
    simpl.
    unfold logrel_cont.
    simpl.
    iDestruct "Hv'" as "(%f & %F & HEQ & %H & #H)".
    rewrite get_val_ITV.
    simpl.
    iRewrite "HEQ".
    rewrite get_fun_fun.
    simpl.
    rewrite hom_vis.
    iIntros (σ) "Hs".
    iApply (wp_subreify with "Hs").
    - simpl.
      rewrite later_map_Next.
      reflexivity.
    - reflexivity.
    - iNext.
      iIntros "Hlc Hs".
      rewrite -!fill_comp H.
      simpl.
      rewrite -Tick_eq.
      iApply wp_tick.
      iNext.
      iSpecialize ("H" $! βv v with "[]"); first done.
      iSpecialize ("H" $! σ with "Hs").
      iApply (wp_wand with "[$H] []").
      iIntros (w) "(%m & %v'' & %σ'' & %Hstep & H)".
      destruct m as [m m'].
      iModIntro.
      iExists ((Nat.add 2 m), m'), v'', σ''. iFrame "H".
      iPureIntro.
      eapply (prim_steps_app (2, 0) (m, m')); eauto.
      term_simpl.
      eapply prim_step_steps.
      eapply Throw_step; reflexivity.
  Qed.


  Lemma compat_callcc {S : Set} (Γ : S -> ty) τ α e :
    ⊢ logrel_valid (Γ ▹ Tcont τ) e α τ -∗
      logrel_valid Γ (Callcc e) (interp_callcc _ α) τ.
  Proof.
    iIntros "#H".
    iIntros (ss γ). iModIntro. iIntros "#Hss".
    iIntros (κ K) "#HK".
    unfold interp_callcc.
    Opaque extend_scope.
    term_simpl.
    iIntros (σ) "Hs".
    rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ (Next ((`κ) (α (extend_scope ss (λit x : IT, Tick ((`κ) x)))))) with "Hs").
    - simpl.
      rewrite ofe_iso_21.
      rewrite later_map_Next.
      do 2 f_equiv; last reflexivity.
      do 5 f_equiv.
      apply bi.siProp.internal_eq_soundness.
      iApply later_equivI_2.
      iNext.
      simpl.
      iApply internal_eq_pointwise.
      iIntros (x).
      simpl.
      rewrite Tick_eq.
      iApply f_equivI.
      rewrite ofe_iso_21.
      done.
    - reflexivity.
    - iNext.
      iIntros "Hlc Hs".
      pose (ss' := (extend_scope ss (λit x : IT, Tick ((`κ) x)))).
      pose (γ' := ((mk_subst (Val (ContV K)%syn)) ∘ (γ ↑)%bind)%bind : inc S [⇒] ∅).
      iSpecialize ("H" $! ss' γ' with "[HK]").
      {
        iIntros (x).
        iModIntro.
        destruct x as [| x]; term_simpl.
        - Transparent extend_scope.
          subst ss'; simpl.
          pose proof (asval_fun (Next (λne x, Tau (laterO_map (`κ) (Next x))))).
          destruct H as [f H].
          rewrite -H.
          iIntros (t r) "#H".
          simpl.
          iApply "H".
          unfold logrel_cont.
          iExists _, K.
          iSplit.
          + rewrite H.
            done.
          + iSplit; first done.
            iModIntro.
            iApply "HK".
        - simpl.
          iApply "Hss".
      }
      iSpecialize ("H" $! κ K with "HK").
      Opaque extend_scope.
      term_simpl.
      iSpecialize ("H" $! σ with "Hs").
      subst ss' γ'.
      iApply (wp_wand with "[$H] []").
      iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H)".
      destruct m as [m m'].
      rewrite -bind_bind_comp' in Hstep.
      iModIntro.
      iExists ((Nat.add 1 m), (Nat.add 1 m')), v'', σ''. iFrame "H".
      iPureIntro.
      eapply (prim_steps_app (1, 1) (m, m')); eauto.
      eapply prim_step_steps.
      eapply Ectx_step; [reflexivity | reflexivity |].
      term_simpl.
      constructor.
  Qed.

  Lemma compat_output {S} Γ (e: expr S) α :
    ⊢ logrel_valid Γ e α Tnat -∗
      logrel_valid Γ (Output e) (interp_output rs α) Tnat.
  Proof.
    iIntros "#H".
    iIntros (ss γ). iModIntro. iIntros "#Hss".
    iIntros (κ K) "#HK".
    term_simpl.
    pose (κ' := OutputSCtx_HOM ss).
    assert ((get_ret OUTPUT (α ss)) = ((`κ') (α ss))) as ->.
    { reflexivity. }
    assert ((`κ) ((`κ') (α ss)) = ((`κ) ◎ (`κ')) (α ss)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }
    assert (fill K (Output (bind γ e))%syn = fill (ectx_compose K (OutputK EmptyK)) (bind γ e)) as ->.
    { rewrite -fill_comp.
      reflexivity.
    }
    iApply obs_ref_bind; first by iApply "H".
    iIntros (βv v). iModIntro. iIntros "#Hv".
    iDestruct "Hv" as (n) "[Hb ->]".
    iRewrite "Hb". simpl.
    iIntros (σ) "Hs".
    rewrite get_ret_ret.
    rewrite hom_vis.
    iApply (wp_subreify with "Hs").
    - simpl.
      rewrite later_map_Next.
      reflexivity.
    - reflexivity.
    - iNext.
      iIntros "Hlc Hs".
      iSpecialize ("HK" $! (RetV 0) (LitV 0) with "[]"); first by iExists 0.
      iSpecialize ("HK" $! (update_output n σ) with "Hs").
      iApply (wp_wand with "[$HK] []").
      iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H')".
      destruct m as [m m'].
      iModIntro.
      iExists ((Nat.add 1 m), (Nat.add 1 m')), v'', σ''. iFrame "H'".
      iPureIntro.
      eapply (prim_steps_app (1, 1) (m, m')); eauto.
      term_simpl.
      eapply prim_step_steps.
      rewrite -fill_comp.
      simpl.
      eapply Ectx_step; [reflexivity | reflexivity |].
      constructor.
      reflexivity.
  Qed.

  Lemma compat_app {S} Γ (e1 e2 : expr S) τ1 τ2 α1 α2 :
  ⊢ logrel_valid Γ e1 α1 (Tarr τ1 τ2) -∗
    logrel_valid Γ e2 α2 τ1 -∗
    logrel_valid Γ (App e1 e2) (interp_app rs α1 α2) τ2.
  Proof.
    iIntros "#H1 #H2".
    iIntros (ss).
    iModIntro.
    iIntros (γ).
    iIntros "#Hss".
    iSpecialize ("H1" with "Hss").
    iSpecialize ("H2" with "Hss").
    unfold interp_app.
    simpl.
    assert ((bind γ (App e1 e2))%syn = (fill (AppRK (bind γ e1) EmptyK) (bind γ e2))) as ->.
    { reflexivity. }
    pose (κ' := (AppRSCtx_HOM α1 ss)).
    assert ((α1 ss ⊙ (α2 ss)) = ((`κ') (α2 ss))) as ->.
    { simpl; unfold AppRSCtx. reflexivity. }
    iIntros (κ K) "#HK".
    assert ((`κ) ((`κ') (α2 ss)) = ((`κ) ◎ (`κ')) (α2 ss)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }
    rewrite fill_comp.
    iApply obs_ref_bind; first by iApply "H2".
    subst sss κ'.
    iIntros (βv v). iModIntro. iIntros "#HV".
    unfold AppRSCtx_HOM; simpl; unfold AppRSCtx.
    rewrite -fill_comp.
    simpl.
    assert ((App (bind γ e1) v) = (fill (AppLK EmptyK v) (bind γ e1))) as ->.
    { reflexivity. }
    pose (κ'' := (AppLSCtx_HOM (IT_of_V βv) ss _)).
    assert (((`κ) (α1 ss ⊙ (IT_of_V βv))) = (((`κ) ◎ (`κ'')) (α1 ss))) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ'')).
    assert ((`κ ◎ `κ'') = (`sss)) as ->.
    { reflexivity. }
    rewrite fill_comp.
    iApply obs_ref_bind; first by iApply "H1".
    iIntros (βv' v'). iModIntro. iIntros "#HV'".
    subst sss κ''.
    rewrite -fill_comp.
    simpl.
    unfold logrel_arr.
    iDestruct "HV'" as "(%f & #Hf & #HV')".
    iRewrite "Hf".
    iSpecialize ("HV'" $! βv v with "HV").
    iApply "HV'"; iApply "HK".
  Qed.

  Lemma compat_nat {S : Set} (Γ : S -> ty) n : ⊢ logrel_valid Γ (# n) (interp_val rs (# n)) ℕ%typ.
  Proof.
    iIntros (ss γ). iModIntro. iIntros "#Hss".
    term_simpl.
    iIntros (κ K) "#HK".
    iSpecialize ("HK" $! (RetV n) (LitV n)).
    rewrite IT_of_V_Ret.
    iApply "HK".
    simpl.
    unfold logrel_nat.
    iExists n; eauto.
  Qed.

  Lemma fundamental {S : Set} (Γ : S -> ty) τ e :
    typed Γ e τ → ⊢ logrel_valid Γ e (interp_expr rs e) τ
  with fundamental_val {S : Set} (Γ : S -> ty) τ v :
    typed_val Γ v τ → ⊢ logrel_valid Γ (Val v) (interp_val rs v) τ.
  Proof.
    - induction 1; simpl.
      + by apply fundamental_val.
      + rewrite -H.
        by apply compat_var.
      + iApply compat_app.
        ++ iApply IHtyped1.
        ++ iApply IHtyped2.
      + iApply compat_natop.
        ++ iApply IHtyped1.
        ++ iApply IHtyped2.
      + iApply compat_if.
        ++ iApply IHtyped1.
        ++ iApply IHtyped2.
        ++ iApply IHtyped3.
      + iApply compat_input.
      + iApply compat_output.
        iApply IHtyped.
      + iApply compat_throw.
        ++ iApply IHtyped1.
        ++ iApply IHtyped2.
      + iApply compat_callcc.
        iApply IHtyped.
    - induction 1; simpl.
      + iApply compat_nat.
      + iApply compat_recV. by iApply fundamental.
  Qed.

End logrel.

Definition κ {S} {E} : ITV E natO → val S :=  λ x,
    match x with
    | core.RetV n => LitV n
    | _ => LitV 0
    end.
Lemma κ_Ret {S} {E} n : κ ((RetV n) : ITV E natO) = (LitV n : val S).
Proof.
  Transparent RetV. unfold RetV. simpl. done. Opaque RetV.
Qed.
Definition rs : gReifiers 1 := gReifiers_cons reify_io gReifiers_nil.

Require Import gitrees.gitree.greifiers.

Lemma logrel_nat_adequacy  Σ `{!invGpreS Σ}`{!statePreG rs natO Σ} {S} (α : IT (gReifiers_ops rs) natO) (e : expr S) n σ σ' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs natO Σ},
      (⊢ logrel rs Tnat α e)%I) →
  ssteps (gReifiers_sReifier rs) α (σ,()) (Ret n) σ' k → ∃ m σ', prim_steps e σ (Val $ LitV n) σ' m.
Proof.
  intros Hlog Hst.
  pose (ϕ := λ (βv : ITV (gReifiers_ops rs) natO),
          ∃ m σ', prim_steps e σ (Val $ κ βv) σ' m).
  cut (ϕ (RetV n)).
  { destruct 1 as ( m' & σ2 & Hm).
    exists m', σ2. revert Hm. by rewrite κ_Ret. }
  eapply (wp_adequacy 0); eauto.
  intros Hinv1 Hst1.
  pose (Φ := (λ (βv : ITV (gReifiers_ops rs) natO), ∃ n, logrel_val rs Tnat (Σ:=Σ) (S:=S) βv (LitV n)
          ∗ ⌜∃ m σ', prim_steps e σ (Val $ LitV n) σ' m⌝)%I).
  assert (NonExpansive Φ).
  { unfold Φ.
    intros l a1 a2 Ha. repeat f_equiv. done. }
  exists Φ. split; first assumption. split.
  { iIntros (βv). iDestruct 1 as (n'') "[H %]".
    iDestruct "H" as (n') "[#H %]". simplify_eq/=.
    iAssert (IT_of_V βv ≡ Ret n')%I as "#Hb".
    { iRewrite "H". iPureIntro. by rewrite IT_of_V_Ret. }
    iAssert (⌜βv = RetV n'⌝)%I with "[-]" as %Hfoo.
    { destruct βv as [r|f]; simpl.
      - iPoseProof (Ret_inj' with "Hb") as "%Hr".
        fold_leibniz. eauto.
      - iExFalso. iApply (IT_ret_fun_ne).
        iApply internal_eq_sym. iExact "Hb". }
    iPureIntro. rewrite Hfoo. unfold ϕ.
    eauto. }
  iIntros "[_ Hs]".
  iPoseProof (Hlog) as "Hlog".
  iAssert (has_substate σ) with "[Hs]" as "Hs".
  { unfold has_substate, has_full_state.
    assert ((of_state rs (IT (sReifier_ops (gReifiers_sReifier rs)) natO) (σ, ())) ≡
            (of_idx rs (IT (sReifier_ops (gReifiers_sReifier rs)) natO) sR_idx (sR_state σ))) as -> ; last done.
    intros j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    { inv_fin j; first done.
      intros i. inversion i. }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
  }
  unshelve epose (idHOM := _ : (HOM rs)).
  { exists idfun. apply IT_hom_idfun. }
  iSpecialize ("Hlog" $! idHOM EmptyK with "[]").
  { iIntros (βv v); iModIntro. iIntros "Hv". iIntros (σ'') "HS".
    iApply wp_val.
    iModIntro.
    iExists (0, 0), v, σ''.
    iSplit; first iPureIntro.
    - apply prim_steps_zero.
    - by iFrame.
  }
  simpl.
  iSpecialize ("Hlog" $! σ with "Hs").
  iApply (wp_wand with"Hlog").
  iIntros ( βv). iIntros "H".
  iDestruct "H" as (m' v σ1' Hsts) "[Hi Hsts]".
  unfold Φ. iDestruct "Hi" as (l) "[Hβ %]". simplify_eq/=.
  iExists l. iModIntro. iSplit; eauto.
  iExists l. iSplit; eauto.
Qed.

Program Definition ı_scope : @interp_scope (gReifiers_ops rs) natO _ Empty_set := λne (x : ∅), match x with end.

Theorem adequacy (e : expr ∅) (k : nat) σ σ' n :
  (empty_env ⊢ e : Tnat)%typing →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) (σ, ()) (Ret k : IT _ natO) σ' n →
  ∃ mm σ', prim_steps e σ (Val $ LitV k) σ' mm.
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs natO]).
  eapply (logrel_nat_adequacy Σ (interp_expr rs e ı_scope)); last eassumption.
  intros ? ?.
  iPoseProof (fundamental rs) as "H".
  { apply Hty. }
  unfold logrel_valid.
  unshelve iSpecialize ("H" $! ı_scope _ with "[]").
  { apply ı%bind. }
  { iIntros (x); destruct x. }
  rewrite ebind_id; first last.
  { intros ?; reflexivity. }
  iApply "H".
Qed.
