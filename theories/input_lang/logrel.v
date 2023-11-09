(** Logical relation for adequacy for the IO lang *)
From Equations Require Import Equations.
From gitrees Require Import gitree.
From gitrees.input_lang Require Import lang interp.

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
  Variable (HCi : ∀ o : opid (sReifier_ops (gReifiers_sReifier rs)),
    CtxIndep (gReifiers_sReifier rs)
      (ITF_solution.IT (sReifier_ops (gReifiers_sReifier rs)) natO) o).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).
  Local Notation tyctx := (tyctx ty).

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
    (∃ n, βv ≡ RetV n ∧ ⌜v = Lit n⌝)%I.
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
  Proof using HCi.
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

  Lemma logrel_step_pure {S} (e' e : expr S) α V :
    (∀ σ, prim_step e σ e' σ (0,0)) →
    logrel_expr V α e' ⊢ logrel_expr V α e.
  Proof.
    intros Hpure.
    iIntros "H".
    iIntros (σ) "Hs".
    iSpecialize ("H" with "Hs").
    iApply (wp_wand with "H").
    iIntros (βv). iDestruct 1 as ([m m'] v σ' Hsteps) "[H2 Hs]".
    iExists (m,m'),v,σ'. iFrame "H2 Hs".
    iPureIntro.
    eapply (prim_steps_app (0,0) (m,m')); eauto.
    { eapply prim_step_steps, Hpure. }
  Qed.

  (* a matching list of closing substitutions *)
  Inductive subs2 : scope → Type :=
  | emp_subs2 : subs2 []
  | cons_subs2 {S} : val [] → ITV → subs2 S → subs2 (()::S)
  .

  Equations subs_of_subs2 {S} (ss : subs2 S) : subs S [] :=
    subs_of_subs2 emp_subs2 v => idsub v;
    subs_of_subs2 (cons_subs2 t α ss) Vz := Val t;
    subs_of_subs2 (cons_subs2 t α ss) (Vs v) := subs_of_subs2 ss v.

  Equations its_of_subs2 {S} (ss : subs2 S) : interp_scope (E:=F) (R:=natO) S :=
    its_of_subs2 emp_subs2 := ();
    its_of_subs2 (cons_subs2 t α ss) := (IT_of_V α, its_of_subs2 ss).

  Equations list_of_subs2 {S} (ss : subs2 S) : list (val []*ITV) :=
    list_of_subs2 emp_subs2 := [];
    list_of_subs2 (cons_subs2 v α ss) := (v,α)::(list_of_subs2 ss).

  Lemma subs_of_emp_subs2 : subs_of_subs2 emp_subs2 ≡ idsub.
  Proof. intros v. dependent elimination v. Qed.

  Definition subs2_valid {S} (Γ : tyctx S) (ss : subs2 S) : iProp :=
    ([∗ list] τx ∈ zip (list_of_tyctx Γ) (list_of_subs2 ss),
      logrel_val (τx.1) (τx.2.2) (τx.2.1))%I.

  Definition logrel_valid {S} (Γ : tyctx S) (e : expr S) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    (∀ ss, subs2_valid Γ ss → logrel τ
                                  (α (its_of_subs2 ss))
                                  (subst_expr e (subs_of_subs2 ss)))%I.

  Lemma compat_var {S} (Γ : tyctx S) (x : var S) τ :
    typed_var Γ x τ → ⊢ logrel_valid Γ (Var x) (interp_var x) τ.
  Proof.
    intros Hx. iIntros (ss) "Hss".
    simp subst_expr.
    iInduction Hx as [|Hx] "IH".
    - dependent elimination ss. simp subs_of_subs2.
      simp interp_var. rewrite /subs2_valid.
      simp list_of_tyctx list_of_subs2 its_of_subs2. simpl.
      iDestruct "Hss" as "[Hv Hss]".
      iApply (logrel_of_val with "Hv").
    - dependent elimination ss. simp subs_of_subs2.
      simp interp_var. rewrite /subs2_valid.
      simp list_of_tyctx list_of_subs2 its_of_subs2. simpl.
      iDestruct "Hss" as "[Hv Hss]". by iApply "IH".
  Qed.

  Lemma compat_if {S} (Γ : tyctx S) (e0 e1 e2 : expr S) α0 α1 α2 τ :
    ⊢ logrel_valid Γ e0 α0  Tnat -∗
      logrel_valid Γ e1 α1 τ -∗
      logrel_valid Γ e2 α2 τ -∗
      logrel_valid Γ (If e0 e1 e2) (interp_if rs α0 α1 α2) τ.
  Proof using HCi.
    iIntros "H0 H1 H2". iIntros (ss) "#Hss".
    simpl. simp subst_expr.
    pose (s := (subs_of_subs2 ss)). fold s.
    iSpecialize ("H0" with "Hss").
    iApply (logrel_bind (IFSCtx (α1 (its_of_subs2 ss)) (α2 (its_of_subs2 ss)))
              [IfCtx (subst_expr e1 s) (subst_expr e2 s)]
                        with "H0").
    iIntros (v βv). iDestruct 1 as (n) "[Hb ->]".
    iRewrite "Hb". simpl.
    unfold IFSCtx.
    destruct (decide (0 < n)).
    - rewrite IF_True//.
      iSpecialize ("H1" with "Hss").
      iApply (logrel_step_pure with "H1").
      intros ?. apply (Ectx_step' []).
      econstructor; eauto.
    - rewrite IF_False; last lia.
      iSpecialize ("H2" with "Hss").
      iApply (logrel_step_pure with "H2").
      intros ?. apply (Ectx_step' []).
      econstructor; eauto. lia.
  Qed.

  Lemma compat_recV {S} Γ (e : expr (()::()::S)) τ1 τ2 α :
    ⊢ □ logrel_valid (consC (Tarr τ1 τ2) (consC τ1 Γ)) e α τ2 -∗
      logrel_valid Γ (Val $ RecV e) (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (ss) "#Hss".
    pose (s := (subs_of_subs2 ss)). fold s.
    pose (env := (its_of_subs2 ss)). fold env.
    simp subst_expr.
    pose (f := (ir_unf rs α env)).
    iAssert (interp_rec rs α env ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf".
    iApply logrel_of_val. iLöb as "IH". iSimpl.
    iExists (Next f). iSplit; eauto.
    iModIntro.
    iIntros (βv w) "#Hw".
    iAssert ((APP' (Fun $ Next f) (IT_of_V βv)) ≡ (Tick (ir_unf rs α env (IT_of_V βv))))%I
      as "Htick".
    { iPureIntro. rewrite APP_APP'_ITV.
      rewrite APP_Fun. simpl. done. }
    iRewrite "Htick". iClear "Htick".
    iIntros (σ) "Hs".
    iApply wp_tick. iNext. simpl.
    pose (ss' := cons_subs2 (RecV (subst_expr e (subs_lift (subs_lift s)))) (FunV (Next (ir_unf rs α env))) (cons_subs2 w βv  ss)).
    iSpecialize ("H" $! ss' with "[Hss]").
    { rewrite {2}/subs2_valid /ss'. simp list_of_tyctx list_of_subs2.
      cbn-[logrel_val]. iFrame "Hss Hw". fold f. iRewrite -"Hf".
      by iApply "IH". }
    iSpecialize ("H"  with "Hs").
    iClear "IH Hss Hw".
    unfold ss'. simpl. simp its_of_subs2. fold f env.
    iRewrite "Hf". simpl.
    iApply (wp_wand with "H").
    iIntros (v).
    iDestruct 1 as ([m m'] v0  σ0 Hsteps) "[Hv Hs]".
    iExists (1+m,0+m'),v0,σ0. iFrame "Hv Hs".
    iPureIntro. econstructor; eauto.
    apply (Ectx_step' []).
    apply BetaS.
    clear.
    unfold subst2.
    rewrite subst_expr_appsub.
    apply subst_expr_proper.
    intro v.
    dependent elimination v.
    { simp subs_of_subs2. unfold appsub.
      simp subs_lift. simp subst_expr.
      simp conssub. reflexivity. }
    dependent elimination v.
    { simp subs_of_subs2. unfold appsub.
      simp subs_lift. unfold expr_lift.
      simp ren_expr. simp subst_expr.
      simp conssub. reflexivity. }
    { simp subs_of_subs2. unfold appsub.
      simp subs_lift. unfold expr_lift.
      fold s. remember (s v) as e1.
      rewrite ren_ren_expr.
      rewrite subst_ren_expr.
      trans (subst_expr e1 idsub).
      - symmetry. apply subst_expr_idsub.
      - apply subst_expr_proper.
        intro v'. simpl. simp conssub.
        reflexivity. }
  Qed.

  Lemma compat_rec {S} Γ (e : expr (()::()::S)) τ1 τ2 α :
    ⊢ □ logrel_valid (consC (Tarr τ1 τ2) (consC τ1 Γ)) e α τ2 -∗
      logrel_valid Γ (Rec e) (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (ss) "#Hss".
    pose (s := (subs_of_subs2 ss)). fold s.
    pose (env := (its_of_subs2 ss)). fold env.
    simp subst_expr.
    iApply (logrel_step_pure (Val (RecV (subst_expr e (subs_lift (subs_lift s)))))).
    { intros ?. eapply (Ectx_step' []). econstructor. }
    iPoseProof (compat_recV with "H") as "H2".
    iSpecialize ("H2" with "Hss").
    simp subst_expr. iApply "H2".
  Qed.

  Lemma compat_app {S} Γ (e1 e2 : expr S) τ1 τ2 α1 α2 :
  ⊢ logrel_valid Γ e1 α1 (Tarr τ1 τ2) -∗
    logrel_valid Γ e2 α2 τ1 -∗
    logrel_valid Γ (App e1 e2) (interp_app rs α1 α2) τ2.
  Proof using HCi.
    iIntros "H1 H2".  iIntros (ss) "#Hss".
    iSpecialize ("H1" with "Hss").
    iSpecialize ("H2" with "Hss").
    pose (s := (subs_of_subs2 ss)). fold s.
    pose (env := its_of_subs2 ss). fold env.
    simp subst_expr. simpl.
    iApply (logrel_bind (AppRSCtx (α1 env)) [AppRCtx (subst_expr e1 s)] with "H2").
    iIntros (v2 β2) "H2". iSimpl.
    iApply (logrel_bind (AppLSCtx (IT_of_V β2)) [AppLCtx v2] with "H1").
    iIntros (v1 β1) "H1". simpl.
    iDestruct "H1" as (f) "[Hα H1]".
    simpl.
    unfold AppLSCtx. iRewrite "Hα". (** XXX why doesn't simpl work here? *)
    iApply ("H1" with "H2").
  Qed.

  Lemma compat_input {S} Γ :
    ⊢ logrel_valid Γ (Input : expr S) (interp_input rs) Tnat.
  Proof.
    iIntros (ss) "Hss".
    iIntros (σ) "Hs".
    destruct (update_input σ) as [n σ'] eqn:Hinp.
    iApply (wp_input with "Hs []"); first eauto.
    iNext. iIntros "Hlc Hs".
    iApply wp_val.
    iExists (1,1),(Lit n),σ'.
    iFrame "Hs". iModIntro. iSplit.
    { iPureIntro.
      simp subst_expr.
      apply prim_step_steps.
      apply (Ectx_step' []).
      by constructor. }
    iExists n. eauto.
  Qed.
  Lemma compat_output {S} Γ (e: expr S) α :
    ⊢ logrel_valid Γ e α Tnat -∗
      logrel_valid Γ (Output e) (interp_output rs α) Tnat.
  Proof using HCi.
    iIntros "H1".
    iIntros (ss) "Hss".
    iSpecialize ("H1" with "Hss").
    pose (s := (subs_of_subs2 ss)). fold s.
    pose (env := its_of_subs2 ss). fold env.
    simp subst_expr. simpl.
    iApply (logrel_bind (get_ret _) [OutputCtx] with "H1").
    iIntros (v βv).
    iDestruct 1 as (m) "[Hb ->]".
    iRewrite "Hb". simpl.
    iIntros (σ) "Hs".
    rewrite get_ret_ret.
    iApply (wp_output with "Hs []"); first done.
    iNext. iIntros "Hlc Hs".
    iExists (1,1),(Lit 0),_.
    iFrame "Hs". iSplit.
    { iPureIntro.
      apply prim_step_steps.
      apply (Ectx_step' []).
      by constructor. }
    iExists 0. eauto.
  Qed.

  Lemma compat_natop {S} (Γ : tyctx S) e1 e2 α1 α2 op :
    ⊢ logrel_valid Γ e1 α1 Tnat -∗
      logrel_valid Γ e2 α2 Tnat -∗
      logrel_valid Γ (NatOp op e1 e2) (interp_natop rs op α1 α2) Tnat.
  Proof using HCi.
    iIntros "H1 H2".  iIntros (ss) "#Hss".
    iSpecialize ("H1" with "Hss").
    iSpecialize ("H2" with "Hss").
    pose (s := (subs_of_subs2 ss)). fold s.
    pose (env := its_of_subs2 ss). fold env.
    simp subst_expr. simpl.
    iApply (logrel_bind (NatOpRSCtx (do_natop op) (α1 env)) [NatOpRCtx op (subst_expr e1 s)] with "H2").
    iIntros (v2 β2) "H2". iSimpl.
    iApply (logrel_bind (NatOpLSCtx (do_natop op) (IT_of_V β2)) [NatOpLCtx op v2] with "H1").
    iIntros (v1 β1) "H1". simpl.
    iDestruct "H1" as (n1) "[Hn1 ->]".
    iDestruct "H2" as (n2) "[Hn2 ->]".
    unfold NatOpLSCtx.
    iAssert ((NATOP (do_natop op) (IT_of_V β1) (IT_of_V β2)) ≡ Ret (do_natop op n1 n2))%I with "[Hn1 Hn2]" as "Hr".
    { iRewrite "Hn1". simpl.
      iRewrite "Hn2". simpl.
      iPureIntro.
      by rewrite NATOP_Ret. }
    iApply (logrel_step_pure (Val (Lit (do_natop op n1 n2)))).
    { intro. apply (Ectx_step' []). constructor.
      destruct op; simpl; eauto. }
    iRewrite "Hr".
    iApply (logrel_of_val (RetV $ do_natop op n1 n2)).
    iExists _. iSplit; eauto.
  Qed.

  Lemma fundamental {S} (Γ : tyctx S) τ e :
    typed Γ e τ → ⊢ logrel_valid Γ e (interp_expr rs e) τ
  with fundamental_val {S} (Γ : tyctx S) τ v :
    typed_val Γ v τ → ⊢ logrel_valid Γ (Val v) (interp_val rs v) τ.
  Proof using HCi.
    - induction 1; simpl.
      + by apply fundamental_val.
      + by apply compat_var.
      + iApply compat_rec. iApply IHtyped.
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
      + iIntros (ss) "Hss". simp subst_expr. simpl.
        iApply (logrel_of_val (RetV n)). iExists n. eauto.
      + iApply compat_recV. by iApply fundamental.
  Qed.

End logrel.

Definition κ {S} {E} : ITV E natO → val S :=  λ x,
    match x with
    | core.RetV n => Lit n
    | _ => Lit 0
    end.
Lemma κ_Ret {S} {E} n : κ ((RetV n) : ITV E natO) = (Lit n : val S).
Proof.
  Transparent RetV. unfold RetV. simpl. done. Opaque RetV.
Qed.
Definition rs : gReifiers 1 := gReifiers_cons reify_io gReifiers_nil.

Lemma logrel_nat_adequacy  Σ `{!invGpreS Σ}`{!statePreG rs natO Σ} {S} (α : IT (gReifiers_ops rs) natO) (e : expr S) n σ σ' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs natO Σ},
      (True ⊢ logrel rs Tnat α e)%I) →
  ssteps (gReifiers_sReifier rs) α (σ,()) (Ret n) σ' k → ∃ m σ', prim_steps e σ (Val $ Lit n) σ' m.
Proof.
  intros Hlog Hst.
  pose (ϕ := λ (βv : ITV (gReifiers_ops rs) natO),
          ∃ m σ', prim_steps e σ (Val $ κ βv) σ' m).
  cut (ϕ (RetV n)).
  { destruct 1 as ( m' & σ2 & Hm).
    exists m', σ2. revert Hm. by rewrite κ_Ret. }
  eapply (wp_adequacy 0); eauto.
  intros Hinv1 Hst1.
  pose (Φ := (λ (βv : ITV (gReifiers_ops rs) natO), ∃ n, logrel_val rs Tnat (Σ:=Σ) (S:=S) βv (Lit n)
          ∗ ⌜∃ m σ', prim_steps e σ (Val $ Lit n) σ' m⌝)%I).
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
    assert (of_state rs (IT (gReifiers_ops rs) natO) (σ, ()) ≡
            of_idx rs (IT (gReifiers_ops rs) natO) sR_idx (sR_state σ)) as -> ; last done.
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


Theorem adequacy (e : expr []) (k : nat) σ σ' n
  (HCi : ∀ o : opid (sReifier_ops (gReifiers_sReifier rs)),
     CtxIndep (gReifiers_sReifier rs) (IT (sReifier_ops (gReifiers_sReifier rs)) natO) o)
  :
  typed empC e Tnat →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ()) (σ,()) (Ret k : IT _ natO) σ' n →
  ∃ mm σ', prim_steps e σ (Val $ Lit k) σ' mm.
Proof.
  intros Hty Hst.
  pose (Σ:=#[invΣ;stateΣ rs natO]).
  eapply (logrel_nat_adequacy Σ (interp_expr rs e ())); last eassumption.
  intros ? ?.
  iPoseProof (fundamental rs) as "H".
  { apply Hty. }
  unfold logrel_valid.
  iIntros "_".
  iSpecialize ("H" $! (emp_subs2 rs)).
  simp its_of_subs2.
  rewrite subs_of_emp_subs2.
  rewrite subst_expr_idsub.
  iApply "H".
  unfold subs2_valid. done.
Qed.
