(** Logical relation for adequacy for the IO lang *)
From gitrees Require Import gitree lang_generic.
From gitrees.examples.input_lang_callcc Require Import lang interp hom.
Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope stdpp_scope.

Section logrel.
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
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

  Definition logrel_ectx {S} V (κ : HOM) (K : ectx S) : iProp :=
    (□ ∀ (βv : ITV) (v : val S), V βv v -∗ obs_ref (`κ (IT_of_V βv)) (fill K (Val v)))%I.

  Definition logrel_expr {S} V (α : IT) (e : expr S) : iProp :=
    (∀ (κ : HOM) (K : ectx S),
       logrel_ectx V κ K -∗ obs_ref (`κ α) (fill K e))%I.

  Definition logrel_arr {S} V1 V2 (βv : ITV) (vf : val S) : iProp :=
    (∃ f, IT_of_V βv ≡ Fun f ∧ □ ∀ αv v, V1 αv v -∗
      logrel_expr V2 (APP' (Fun f) (IT_of_V αv)) (App (Val vf) (Val v)))%I.


  Definition logrel_cont {S} V (βv : ITV) (v : val S) : iProp :=
    (∃ (κ : HOM) K, (IT_of_V βv) ≡ (Fun (Next (λne x, Tau (laterO_map (`κ) (Next x)))))
                            ∧ ⌜v = ContV K⌝
                            ∧ □ logrel_ectx V κ K)%I.

  Fixpoint logrel_val {S} (τ : ty) : ITV → (val S) → iProp
    := match τ with
       | Tnat => logrel_nat
       | Tarr τ1 τ2 => logrel_arr (logrel_val τ1) (logrel_val τ2)
       | Tcont τ => logrel_cont (logrel_val τ)
       end.

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
    Proper ((≡) ==> (≡) ==> (≡)) V →
    Proper ((≡) ==> (≡) ==> (≡)) (logrel_expr V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_nat_proper {S} :
    Proper ((≡) ==> (≡) ==> (≡)) (@logrel_nat S).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_val_proper {S} (τ : ty) :
    Proper ((≡) ==> (≡) ==> (≡)) (@logrel_val S τ).
  Proof.
    induction τ; simpl; solve_proper.
  Qed.

  #[export] Instance logrel_ectx_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V →
    Proper ((≡) ==> (≡) ==> (≡)) (logrel_ectx V).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_arr_proper {S} (V1 V2 : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V1 ->
    Proper ((≡) ==> (≡) ==> (≡)) V2 →
    Proper ((≡) ==> (≡) ==> (≡)) (logrel_arr V1 V2).
  Proof.
    solve_proper.
  Qed.

  #[export] Instance logrel_cont_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V ->
    Proper ((≡) ==> (≡) ==> (≡)) (logrel_cont V).
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
    logrel_val τ αv v -∗ logrel τ (IT_of_V αv) (Val v).
  Proof.
    iIntros "H1". iIntros (κ K) "HK".
    iIntros (σ) "Hs".
    by iApply ("HK" $! αv v with "[$H1] [$Hs]").
  Qed.

  Lemma logrel_head_step_pure_ectx {S} n K (e' e : expr S) α V :
    (∀ σ K, head_step e σ e' σ K (n, 0)) →
    ⊢ logrel_expr V α (fill K e') -∗ logrel_expr V α (fill K e).
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

  Lemma obs_ref_bind {S} (f : HOM) (K : ectx S) e α τ1 :
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

  Lemma compat_var {S : Set} (Γ : S -> ty) (x : S) :
    ⊢ logrel_valid Γ (Var x) (interp_var x) (Γ x).
  Proof.
    iModIntro. iIntros (ss γ) "Hss". iApply "Hss".
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
    iApply (logrel_head_step_pure_ectx _ EmptyK _
              ((rec bind γ1 e)%syn v)
              (Tick (later_car (Next f) (IT_of_V αv)))
           (logrel_val τ2) with "[]"); last first.
    + rewrite {2}/ss'. rewrite /f.
      iIntros (κ K) "#HK". iIntros (σ) "Hs".
      rewrite hom_tick. iApply wp_tick. iNext.
      iApply "H"; eauto.
      rewrite /ss' /γ'.
      iIntros (x'); destruct x' as [| [| x']]; term_simpl; iModIntro.
      * by iApply logrel_of_val.
      * iRewrite "Hf".
        iIntros (κ' K') "#HK'".
        iApply "HK'".
        simpl.
        unfold logrel_arr.
        iExists (Next (ir_unf rs α env)).
        iSplit; first done.
        iModIntro.
        iApply "IH".
      * iApply "Henv".
    + term_simpl. intros. subst γ1 γ'.
      rewrite -!bind_bind_comp'.
      apply BetaS.
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
    simpl.
    pose (κ' := (IFSCtx_HOM (α1 ss) (α2 ss))).
    assert ((IF (α0 ss) (α1 ss) (α2 ss)) = ((`κ') (α0 ss))) as -> by reflexivity.
    term_simpl.
    iIntros (κ K) "#HK".
    assert ((`κ) ((IFSCtx (α1 ss) (α2 ss)) (α0 ss)) = ((`κ) ◎ (`κ')) (α0 ss))
      as -> by reflexivity.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.
    assert (fill K (If (bind γ e0) (bind γ e1) (bind γ e2))%syn =
            fill (ectx_compose K (IfK EmptyK (bind γ e1) (bind γ e2))) (bind γ e0)) as ->.
    { rewrite -fill_comp. reflexivity. }
    iApply (obs_ref_bind with "[H0] [H1 H2]"); first by iApply "H0".
    iIntros (βv v). iModIntro. iIntros "#HV".
    term_simpl.
    unfold logrel_nat.
    iDestruct "HV" as "(%n & #Hn & ->)".
    iRewrite "Hn".
    unfold IFSCtx.
    destruct (decide (0 < n)) as [H|H].
    - rewrite -fill_comp.
      simpl.
      rewrite IF_True//.
      iSpecialize ("H1" with "Hss").
      term_simpl. rewrite /logrel.
      iPoseProof (logrel_head_step_pure_ectx _ EmptyK
                    (bind γ e1)%syn _ (α1 ss) (logrel_val τ) with "H1")
        as "Hrel"; last iApply  ("Hrel" $! κ K with "HK").
      intros σ K0. by apply IfTrueS.
    - rewrite -fill_comp.
      simpl.
      unfold IFSCtx.
      rewrite IF_False//; last lia.
      iSpecialize ("H2" with "Hss").
      term_simpl. rewrite /logrel.
      iPoseProof (logrel_head_step_pure_ectx _ EmptyK
                    (bind γ e2)%syn _ (α2 ss) (logrel_val τ) with "H2")
        as "Hrel"; last iApply ("Hrel" $! κ K with "HK").
      intros σ K0. apply IfFalseS. lia.
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
    iApply (wp_input' with "Hs []"); first done.
    iNext. iIntros "Hlc Hs". term_simpl.
    iSpecialize ("HK" $! (RetV n) (LitV n) with "[]"); first by iExists n.
    iSpecialize ("HK" $! σ' with "Hs").
    rewrite IT_of_V_Ret.
    iApply (wp_wand with "[$HK] []").
    iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H)".
    iModIntro.
    destruct m as [m1 m2].
    iExists ((Nat.add 1 m1), (Nat.add 1 m2)), v'', σ''. iFrame "H".
    iPureIntro.
    eapply (prim_steps_app (1, 1) (m1, m2)); eauto.
    eapply prim_step_steps.
    eapply Ectx_step; [reflexivity | reflexivity |].
    by constructor.
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
    iIntros (κ K) "#HK".
    set (κ' := (NatOpRSCtx_HOM op α1 ss)).
    assert ((NATOP (do_natop op) (α1 ss) (α2 ss)) = ((`κ') (α2 ss))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.
    assert (fill K (NatOp op (bind γ e1) (bind γ e2))%syn =
            fill (ectx_compose K (NatOpRK op (bind γ e1) EmptyK)) (bind γ e2)) as ->.
    { rewrite -fill_comp. reflexivity. }
    iApply (obs_ref_bind with "H2").
    iIntros (βv v). iModIntro. iIntros "(%n2 & #HV & ->)".
    term_simpl. clear κ' sss.
    rewrite -fill_comp. simpl.
    pose (κ' := (NatOpLSCtx_HOM op (IT_of_V βv) ss _)).
    assert ((NATOP (do_natop op) (α1 ss) (IT_of_V βv)) = ((`κ') (α1 ss))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.
    assert (fill K (NatOp op (bind γ e1) (LitV n2))%syn =
            fill (ectx_compose K (NatOpLK op EmptyK (LitV n2))) (bind γ e1)) as ->.
    { rewrite -fill_comp. reflexivity. }
    iApply (obs_ref_bind with "H1").
    subst sss κ'.
    term_simpl.
    iIntros (t r). iModIntro. iIntros "(%n1 & #H & ->)".
    simpl.
    iAssert ((NATOP (do_natop op) (IT_of_V t) (IT_of_V βv)) ≡ Ret (do_natop op n1 n2))%I with "[HV H]" as "Hr".
    { iRewrite "HV". simpl.
      iRewrite "H". simpl.
      iPureIntro.
      by rewrite NATOP_Ret.
    }
    rewrite -fill_comp. simpl.
    iApply (logrel_head_step_pure_ectx _ EmptyK (Val (LitV (do_natop op n1 n2))) with "[]");
      last done; last first.
    + simpl. iRewrite "Hr". iApply (logrel_of_val Tnat (RetV (do_natop op n1 n2))). term_simpl.
      iExists _. iSplit; eauto.
    + intros. by constructor.
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
    assert ((interp_throw rs α β ss) = ((`κ') (α ss))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.
    assert (fill K (Throw (bind γ e) (bind γ e'))%syn =
            fill (ectx_compose K (ThrowLK  EmptyK (bind γ e'))) (bind γ e))
      as -> by by rewrite -fill_comp.
    iApply obs_ref_bind; first by iApply "H1".
    iIntros (βv v). iModIntro. iIntros "#Hv".
    Transparent interp_throw.
    simpl.
    rewrite get_val_ITV' -!fill_comp.
    simpl.
    pose (κ'' := ThrowRSCtx_HOM (IT_of_V βv) ss _).
    assert ((get_fun (λne f : laterO (IT -n> IT), THROW (IT_of_V βv) f) (β ss)) ≡
              ((`κ'') (β ss))) as ->.
    {
      subst κ''. simpl. by rewrite get_val_ITV.
    }
    rewrite HOM_ccompose.
    pose (sss' := (HOM_compose κ κ'')). rewrite (HOM_compose_ccompose κ κ'' sss')//.
    assert (fill K (Throw v (bind γ e'))%syn =
            fill (ectx_compose K (ThrowRK v EmptyK)) (bind γ e'))
      as -> by by rewrite -fill_comp.
    iApply obs_ref_bind; first by iApply "H2".
    iIntros (βv' v'). iModIntro. iIntros "#Hv'".
    Transparent interp_throw.
    simpl.
    unfold logrel_cont.
    iDestruct "Hv'" as "(%f & %F & HEQ & %H & #H)".
    rewrite get_val_ITV.
    simpl.
    iRewrite "HEQ".
    rewrite get_fun_fun.
    simpl.
    iIntros (σ) "Hs".
    iApply (wp_throw' with "Hs []").
    iNext. iIntros "Hcl Hs". term_simpl.
    rewrite later_map_Next. iApply wp_tick. iNext.
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
    eapply Throw_step; last done.
    rewrite H. by rewrite -!fill_comp.
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

    iApply (wp_callcc with "Hs []").
    iNext. iIntros "Hcl Hs". term_simpl.

    pose (ff := (λit x : IT, Tick ((`κ) x))).
    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ extend_scope ss )?f] => set (fff := f)
    end.
    assert (ff ≡ fff) as <-.
    {
      subst ff fff. do 1 f_equiv.
      epose proof (contractive_proper Next).
      rewrite H; first reflexivity.
      rewrite ofe_mor_ext. intro. simpl.
      by rewrite later_map_Next.
    }
    pose (ss' := (extend_scope ss ff)).
    pose (γ' := ((mk_subst (Val (ContV K)%syn)) ∘ (γ ↑)%bind)%bind : inc S [⇒] ∅).
    iSpecialize ("H" $! ss' γ' with "[HK]").
    {
      iIntros (x). iModIntro.
      destruct x as [| x]; term_simpl; last iApply "Hss".
      Transparent extend_scope.
      subst ss'; simpl.
      pose proof (asval_fun (Next (λne x, Tau (laterO_map (`κ) (Next x))))).
      subst ff. destruct H as [f H].
      iIntros (t r) "#H".
      simpl. rewrite -H. iApply "H".
      unfold logrel_cont.
      iExists κ, K.
      iSplit; first done.
      iSplit; first done.
      iModIntro.
      iApply "HK".
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
    replace (get_ret OUTPUT (α ss)) with ((`κ') (α ss)) by reflexivity.
    replace ((`κ) ((`κ') (α ss))) with (((`κ) ◎ (`κ')) (α ss)) by reflexivity.
    pose (sss := (HOM_compose κ κ')).
    replace (`κ ◎ `κ') with  (`sss) by reflexivity.
    assert (fill K (Output (bind γ e))%syn =
            fill (ectx_compose K (OutputK EmptyK)) (bind γ e)) as ->.
    { rewrite -fill_comp. reflexivity. }
    iApply obs_ref_bind; first by iApply "H".
    iIntros (βv v). iModIntro. iIntros "#Hv".
    iDestruct "Hv" as (n) "[Hb ->]".
    iRewrite "Hb". simpl.
    iIntros (σ) "Hs".
    rewrite get_ret_ret.
    iApply (wp_output' with "Hs []"); first done.
    iNext. iIntros "Hlc Hs".
    iSpecialize ("HK" $! (RetV 0) (LitV 0) with "[]"); first by iExists 0.
    iSpecialize ("HK" $! (update_output n σ) with "Hs").
    iApply (wp_wand with "[$HK] []").
    iIntros (v') "(%m & %v'' & %σ'' & %Hstep & H')".
    destruct m as [m m'].
    iModIntro.
    iExists ((Nat.add 1 m), (Nat.add 1 m')), v'', σ''. iFrame "H'".
    iPureIntro.
    eapply (prim_steps_app (1, 1) (m, m')); eauto.
    eapply prim_step_steps.
    rewrite -fill_comp.
    eapply Ectx_step; [reflexivity | reflexivity |].
    by constructor.
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

  Lemma compat_nat {S : Set} (Γ : S -> ty) n :
    ⊢ logrel_valid Γ (# n)%syn (interp_val rs (# n)%syn) ℕ%typ.
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
    - intros H.
      induction H.
      + by iApply fundamental_val.
      + rewrite -H.
        by iApply compat_var.
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
Definition rs : gReifiers CtxDep 1 := gReifiers_cons reify_io gReifiers_nil.

Lemma logrel_nat_adequacy  Σ `{!invGpreS Σ} `{!statePreG rs natO Σ} {S}
  (α : IT (gReifiers_ops rs) natO)
  (e : expr S) n σ σ' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs natO Σ}, (⊢ logrel rs Tnat α e)%I) →
  ssteps (gReifiers_sReifier rs) α (σ, ()) (Ret n) σ' k →
  ∃ m σ', prim_steps e σ (Val $ LitV n) σ' m.
Proof.
  intros Hlog Hst.
  pose (ϕ := λ (βv : ITV (gReifiers_ops rs) natO),
          ∃ m σ', prim_steps e σ (Val $ κ βv) σ' m).
  cut (ϕ (RetV n)).
  {
    destruct 1 as ( m' & σ2 & Hm).
    exists m', σ2. revert Hm. by rewrite κ_Ret.
  }
  eapply (wp_adequacy 0); eauto.
  intros Hinv1 Hst1.
  pose (Φ := (λ (βv : ITV (gReifiers_ops rs) natO),
                ∃ n, logrel_val rs Tnat (Σ:=Σ) (S:=S) βv (LitV n)
                     ∗ ⌜∃ m σ', prim_steps e σ (Val $ LitV n) σ' m⌝)%I).
  assert (NonExpansive Φ).
  {
    unfold Φ.
    intros l a1 a2 Ha. repeat f_equiv. done.
  }
  exists Φ. split; first assumption. split.
  - iIntros (βv). iDestruct 1 as (n'') "[H %]".
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
    eauto.
  - iIntros "[_ Hs]".
    iPoseProof (Hlog) as "Hlog".
    iAssert (has_substate σ) with "[Hs]" as "Hs".
    {
      unfold has_substate, has_full_state.
      assert ((of_state rs (IT (sReifier_ops (gReifiers_sReifier rs)) natO) (σ, ())) ≡
                (of_idx rs (IT (sReifier_ops (gReifiers_sReifier rs)) natO) sR_idx (sR_state σ)))
        as -> ; last done.
      intros j. unfold sR_idx. simpl.
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
    iSpecialize ("Hlog" $! HOM_id EmptyK with "[]").
    {
      iIntros (βv v); iModIntro. iIntros "Hv". iIntros (σ'') "HS".
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

Theorem adequacy (e : expr ∅) (k : nat) σ σ' n :
  typed □ e Tnat →
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
