(** Logical relation for adequacy for the IO lang *)
From gitrees Require Import gitree lang_generic.
From gitrees.examples.input_lang Require Import lang interp.
Require Import gitrees.gitree.greifiers.
Require Import Binding.Lib Binding.Set Binding.Env.

Section logrel.
  Context {sz : nat}.
  Variable (rs : gReifiers NotCtxDep sz).
  Context {subR : subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F natO).
  Notation ITV := (ITV F natO).
  Context `{!invGS Σ, !stateG rs natO Σ}.
  Notation iProp := (iProp Σ).
  Notation restO := (gState_rest sR_idx rs ♯ IT).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).

  Notation "'WP' α {{ β , Φ } }" := (wp rs α notStuck ⊤ (λ β, Φ))
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  β ,  Φ  } }") : bi_scope.

  Notation "'WP' α {{ Φ } }" := (wp rs α notStuck ⊤ Φ)
    (at level 20, α, Φ at level 200,
     format "'WP'  α  {{  Φ  } }") : bi_scope.

  Definition logrel_expr {S} V (α : IT) (e : expr S) : iProp :=
    (∀ (σ : stateO),
        has_substate σ -∗
        WP α {{ βv, ∃ m v σ', ⌜prim_steps e σ (Val v) σ' m⌝
                         ∗ V βv v ∗ has_substate σ' }})%I.
  Definition logrel_nat {S} (βv : ITV) (v : val S) : iProp :=
    (∃ n, βv ≡ RetV n ∧ ⌜v = LitV n⌝)%I.
  Definition logrel_arr {S} V1 V2 (βv : ITV) (vf : val S) : iProp :=
    (∃ f, IT_of_V βv ≡ Fun f ∧ □ ∀ αv v, V1 αv v -∗ logrel_expr V2 (APP' (Fun f) (IT_of_V αv)) (App (Val vf) (Val v)))%I.

  Fixpoint logrel_val (τ : ty) {S} : ITV → (val S) → iProp
    := match τ with
       | Tnat => logrel_nat
       | Tarr τ1 τ2 => logrel_arr (logrel_val τ1) (logrel_val τ2)
       end.

  Definition logrel (τ : ty) {S} : IT → (expr S) → iProp
    := logrel_expr (logrel_val τ).

  #[export] Instance logrel_expr_ne {S} (V : ITV → val S → iProp) :
    NonExpansive2 V → NonExpansive2 (logrel_expr V).
  Proof. solve_proper. Qed.
  #[export] Instance logrel_nat_ne {S} : NonExpansive2 (@logrel_nat S).
  Proof. solve_proper. Qed.
  #[export] Instance logrel_val_ne (τ : ty) {S} : NonExpansive2 (@logrel_val τ S).
  Proof. induction τ; simpl; solve_proper. Qed.
  #[export] Instance logrel_expr_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V →
    Proper ((≡) ==> (≡) ==> (≡)) (logrel_expr V).
  Proof. solve_proper. Qed.
  #[export] Instance logrel_val_proper (τ : ty) {S} :
    Proper ((≡) ==> (≡) ==> (≡)) (@logrel_val τ S).
  Proof. induction τ; simpl; solve_proper. Qed.
  #[export] Instance logrel_persistent (τ : ty) {S} α v :
    Persistent (@logrel_val τ S α v).
  Proof.
    revert α v. induction τ=> α v; simpl.
    - unfold logrel_nat. apply _.
    - unfold logrel_arr. apply _.
  Qed.

  Lemma logrel_bind {S} (f : IT → IT) (K : ectx S) `{!IT_hom f}
    e α τ1 V2 `{!NonExpansive2 V2} :
    ⊢ logrel_expr (logrel_val τ1) α e -∗
      (∀ v βv, logrel_val τ1 βv v -∗
                   logrel_expr V2 (f (IT_of_V βv)) (fill K (Val v))) -∗
      logrel_expr V2 (f α) (fill K e).
  Proof.
    iIntros "H1 H2".
    iLöb as "IH" forall (α e).
    iIntros (σ) "Hs".
    iApply wp_bind.
    { solve_proper. }
    iSpecialize ("H1" with "Hs").
    iApply (wp_wand with "H1").
    iIntros (αv). iDestruct 1 as ([m m'] v σ' Hsteps) "[H1 Hs]".
    apply (prim_steps_ctx K) in Hsteps.
    iSpecialize ("H2" with "H1 Hs").
    iApply (wp_wand with "H2"). iModIntro.
    iIntros (βv). iDestruct 1 as ([m2 m2'] v2 σ2' Hsteps2) "[H2 Hs]".
    iExists (m + m2, m' + m2'),v2,σ2'. iFrame "H2 Hs".
    iPureIntro. eapply (prim_steps_app (m,m') (m2,m2')); eauto.
  Qed.

  Lemma logrel_of_val {S} αv (v : val S) V :
    V αv v -∗ logrel_expr V (IT_of_V αv) (Val v).
  Proof.
    iIntros "H1". iIntros (σ) "Hs".
    iApply wp_val.
    iExists (0,0),v,σ. iFrame. iPureIntro.
    by econstructor.
  Qed.

  Lemma logrel_step_pure {S} n (e' e : expr S) α V :
    (∀ σ, prim_step e σ e' σ (n,0)) →
    logrel_expr V α e' ⊢ logrel_expr V α e.
  Proof.
    intros Hpure.
    iIntros "H".
    iIntros (σ) "Hs".
    iSpecialize ("H" with "Hs").
    iApply (wp_wand with "H").
    iIntros (βv). iDestruct 1 as ([m m'] v σ' Hsteps) "[H2 Hs]".
    iExists ((Nat.add n m),m'),v,σ'. iFrame "H2 Hs".
    iPureIntro.
    eapply (prim_steps_app (n,0) (m,m')); eauto.
    { eapply prim_step_steps, Hpure. }
  Qed.

  Definition ssubst2_valid {S : Set}
    (Γ : S -> ty)
    (ss : @interp_scope F natO _ S)
    (γ : S [⇒] Empty_set) : iProp :=
    (∀ x, □ logrel (Γ x) (ss x) (γ x))%I.

  Definition logrel_valid {S : Set}
    (Γ : S -> ty)
    (e : expr S)
    (α : @interp_scope F natO _ S -n> IT)
    (τ : ty) : iProp :=
    (□ ∀ (ss : @interp_scope F natO _ S)
       (γ : S [⇒] Empty_set),
       ssubst2_valid Γ ss γ → logrel τ (α ss) (bind γ e))%I.

  Lemma compat_var {S : Set} (Γ : S → ty) (x : S):
    ⊢ logrel_valid Γ (Var x) (interp_var x) (Γ x).
  Proof.
    iModIntro. iIntros (ss γ) "Hss". iApply "Hss".
  Qed.

  Lemma compat_if {S : Set} (Γ : S → ty) (e0 e1 e2 : expr S) α0 α1 α2 τ :
    ⊢ logrel_valid Γ e0 α0  Tnat -∗
      logrel_valid Γ e1 α1 τ -∗
      logrel_valid Γ e2 α2 τ -∗
      logrel_valid Γ (If e0 e1 e2) (interp_if rs α0 α1 α2) τ.
  Proof.
    iIntros "#H0 #H1 #H2".
    iModIntro.
    iIntros (ss γ) "#Hss".
    simpl.
    iSpecialize ("H0" with "Hss").
    term_simpl.
    iApply (@logrel_bind Empty_set
              (IFSCtx (α1 ss) (α2 ss))
              (IfK EmptyK (bind γ e1) (bind γ e2)) _ (bind γ e0) (α0 ss) Tnat with "H0").
    iIntros (v βv). iDestruct 1 as (n) "[Hb ->]".
    iRewrite "Hb". simpl.
    unfold IFSCtx.
    destruct (decide (0 < n)).
    - rewrite IF_True; last done.
      iSpecialize ("H1" with "Hss").
      iApply (logrel_step_pure with "H1").
      intros ?. apply (Ectx_step' EmptyK).
      econstructor; eauto.
    - rewrite IF_False; last lia.
      iSpecialize ("H2" with "Hss").
      iApply (logrel_step_pure with "H2").
      intros ?. apply (Ectx_step' EmptyK).
      econstructor; eauto. lia.
  Qed.

  Lemma compat_recV {S : Set} (Γ : S -> ty) (e : expr (inc (inc S))) τ1 τ2 α :
    ⊢ □ logrel_valid ((Γ ▹ (Tarr τ1 τ2) ▹ τ1)) e α τ2 -∗
      logrel_valid Γ (Val $ RecV e) (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H !> %env %γ #Henv".
    set (f := (ir_unf rs α env)).
    iAssert (interp_rec rs α env ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf".
    Opaque IT_of_V.
    iApply logrel_of_val; term_simpl.
    iExists _. iSplit.
    { iPureIntro. apply into_val. }
    iModIntro.
    iLöb as "IH".
    iIntros (αv v) "#Hw".
    rewrite APP_APP'_ITV APP_Fun laterO_map_Next -Tick_eq.
    pose (ss' := (extend_scope (extend_scope env (interp_rec rs α env)) (IT_of_V αv))).
    set (γ' := ((mk_subst (Val (rec bind ((γ ↑) ↑)%bind e)%syn))
                   ∘ ((mk_subst (shift (Val v))) ∘ ((γ ↑) ↑)))%bind).
    rewrite /logrel.
    iSpecialize ("H" $! ss' γ').
    set (γ1 := ((γ ↑) ↑)%bind).
    iApply (logrel_step_pure 1 ((bind γ' e)%syn) with "[]").
    {
      intros ?. eapply (Ectx_step' EmptyK). term_simpl. subst γ1 γ'.
      rewrite -!bind_bind_comp'.
      apply BetaS.
    }
    rewrite {2}/ss'. rewrite /f.
    iIntros (σ) "Hs".
    iApply wp_tick. iNext.
    iApply "H"; eauto; iClear "H".
    rewrite /ss' /γ'.
    iIntros (x'); destruct x' as [| [| x']]; term_simpl; iModIntro.
    * by iApply logrel_of_val.
    * iRewrite "Hf".
      iApply logrel_of_val.
      simpl.
      iExists (Next (ir_unf rs α env)).
      iSplit; first done.
      iModIntro.
      iApply "IH".
    * iApply "Henv".
  Qed.

  Lemma compat_app {S : Set} (Γ : S → ty) (e1 e2 : expr S) τ1 τ2 α1 α2 :
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
    iApply (logrel_bind (AppRSCtx (α1 ss)) (AppRK (bind γ e1) EmptyK) with "H2").
    iIntros (v2 β2) "#H2'". iSimpl.
    iApply (logrel_bind (AppLSCtx (IT_of_V β2)) (AppLK EmptyK v2) with "H1").
    iIntros (v1 β1) "#H1'". iSimpl.
    iDestruct "H1'" as (f) "[Hα H1']".
    simpl.
    unfold AppLSCtx. iRewrite "Hα".
    iApply ("H1'" with "H2'").
  Qed.

  Lemma compat_input {S : Set} (Γ : S → ty) :
    ⊢ logrel_valid Γ (Input : expr S) (interp_input rs) Tnat.
  Proof.
    iModIntro.
    iIntros (ss γ) "Hss".
    iIntros (σ) "Hs".
    destruct (update_input σ) as [n σ'] eqn:Hinp.
    iApply (wp_input with "Hs []"); first eauto.
    iNext. iIntros "Hlc Hs".
    iApply wp_val.
    iExists (1,1),(LitV n),σ'.
    iFrame "Hs". iModIntro. iSplit.
    { iPureIntro.
      term_simpl.
      apply prim_step_steps.
      apply (Ectx_step' EmptyK).
      by constructor.
    }
    iExists n. eauto.
  Qed.

  Lemma compat_output {S : Set} (Γ : S → ty) (e: expr S) α :
    ⊢ logrel_valid Γ e α Tnat -∗
      logrel_valid Γ (Output e) (interp_output rs α) Tnat.
  Proof.
    iIntros "#H1".
    iModIntro.
    iIntros (ss γ) "#Hss".
    iSpecialize ("H1" with "Hss").
    term_simpl.
    iApply (logrel_bind (get_ret _) (OutputK EmptyK) with "H1").
    iIntros (v βv).
    iDestruct 1 as (m) "[Hb ->]".
    iRewrite "Hb". simpl.
    iIntros (σ) "Hs".
    rewrite get_ret_ret.
    iApply (wp_output with "Hs []"); first done.
    iNext. iIntros "Hlc Hs".
    iExists (1,1),(LitV 0),_.
    iFrame "Hs". iSplit.
    { iPureIntro.
      apply prim_step_steps.
      apply (Ectx_step' EmptyK).
      by constructor. }
    iExists 0. eauto.
  Qed.

  Lemma compat_natop {S : Set} (Γ : S → ty) e1 e2 α1 α2 op :
    ⊢ logrel_valid Γ e1 α1 Tnat -∗
      logrel_valid Γ e2 α2 Tnat -∗
      logrel_valid Γ (NatOp op e1 e2) (interp_natop rs op α1 α2) Tnat.
  Proof.
    iIntros "#H1 #H2". iModIntro. iIntros (ss γ) "#Hss".
    iSpecialize ("H1" with "Hss").
    iSpecialize ("H2" with "Hss").
    term_simpl.
    iApply (logrel_bind (NatOpRSCtx (do_natop op) (α1 ss)) (NatOpRK op (bind γ e1) EmptyK) with "H2").
    iIntros (v2 β2) "H2'". iSimpl.
    iApply (logrel_bind (NatOpLSCtx (do_natop op) (IT_of_V β2)) (NatOpLK op EmptyK v2) with "H1").
    iIntros (v1 β1) "H1'". simpl.
    iDestruct "H1'" as (n1) "[Hn1 ->]".
    iDestruct "H2'" as (n2) "[Hn2 ->]".
    unfold NatOpLSCtx.
    iAssert ((NATOP (do_natop op) (IT_of_V β1) (IT_of_V β2)) ≡ Ret (do_natop op n1 n2))%I with "[Hn1 Hn2]" as "Hr".
    { iRewrite "Hn1". simpl.
      iRewrite "Hn2". simpl.
      iPureIntro.
      by rewrite NATOP_Ret. }
    iApply (logrel_step_pure _ (Val (LitV (do_natop op n1 n2)))).
    { intro. apply (Ectx_step' EmptyK). constructor.
      destruct op; simpl; eauto. }
    iRewrite "Hr".
    iApply (logrel_of_val (RetV $ do_natop op n1 n2)).
    iExists _. iSplit; eauto.
  Qed.

  Lemma fundamental {S : Set} (Γ : S → ty) τ e :
    typed Γ e τ → ⊢ logrel_valid Γ e (interp_expr rs e) τ
  with fundamental_val {S : Set} (Γ : S → ty) τ v :
    typed_val Γ v τ → ⊢ logrel_valid Γ (Val v) (interp_val rs v) τ.
  Proof.
    - induction 1; simpl.
      + by apply fundamental_val.
      + subst.
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
    - induction 1; simpl.
      + iModIntro. iIntros (ss γ) "Hss". term_simpl.
        iApply (logrel_of_val (RetV n)). iExists n. eauto.
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
Definition rs : gReifiers NotCtxDep 1 := gReifiers_cons reify_io gReifiers_nil.

Lemma logrel_nat_adequacy  Σ `{!invGpreS Σ}`{!statePreG rs natO Σ} {S} (α : IT (gReifiers_ops rs) natO) (e : expr S) n σ σ' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs natO Σ},
      (True ⊢ logrel rs Tnat α e)%I) →
  ssteps (gReifiers_sReifier NotCtxDep rs) α (σ,()) (Ret n) σ' k → ∃ m σ', prim_steps e σ (Val $ LitV n) σ' m.
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
  iPoseProof (Hlog with "[//]") as "Hlog".
  iAssert (has_substate σ) with "[Hs]" as "Hs".
  { unfold has_substate, has_full_state.
    assert (of_state NotCtxDep rs (IT (gReifiers_ops rs) natO) (σ, ()) ≡
            of_idx NotCtxDep rs (IT (gReifiers_ops rs) natO) 0 σ)%stdpp as ->; last done.
    intro j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    { inv_fin j; first done.
      intros i. inversion i. }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
  }
  iSpecialize ("Hlog" $! σ with "Hs").
  iApply (wp_wand with"Hlog").
  iIntros ( βv). iIntros "H".
  iDestruct "H" as (m' v σ1' Hsts) "[Hi Hsts]".
  unfold Φ. iDestruct "Hi" as (l) "[Hβ %]". simplify_eq/=.
  iExists l. iModIntro. iSplit; eauto.
  iExists l. iSplit; eauto.
Qed.

Theorem adequacy (e : expr ∅) (k : nat) σ σ' n :
  typed □ e Tnat →
  ssteps (gReifiers_sReifier NotCtxDep rs) (interp_expr rs e ı_scope) (σ,()) (Ret k : IT _ natO) σ' n →
  ∃ mm σ', prim_steps e σ (Val $ LitV k) σ' mm.
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs natO]).
  eapply (logrel_nat_adequacy Σ (interp_expr rs e ı_scope)); last eassumption.
  intros ? ?.
  iPoseProof (fundamental rs) as "H".
  { apply Hty. }
  unfold logrel_valid.
  iIntros "_".
  unshelve iSpecialize ("H" $! ı_scope _ with "[]").
  { apply ı%bind. }
  { iIntros (x); destruct x. }
  rewrite ebind_id; first last.
  { intros ?; reflexivity. }
  iApply "H".
Qed.
