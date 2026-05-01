(* Adequacy of the gitrees denotational semantics with respect to the operational semantics for the PRNG language.
   gitree interpretation steps implies PRNG operational semantics steps.

   Soundness, the converse, that PRNG operational semantics steps implies gitree interpretation steps, is already proved [prng_lang/interp.v]
 *)
From gitrees Require Import gitree program_logic lang_generic.
From gitrees.examples.prng_lang Require Import lang interp prng_seed_combinator.
From gitrees.effects Require Import prng.

Require Import Binding.Lib Binding.Set Binding.Env.

Import IF_nat.

Section prng_logrel.
  Context {Rng : Prng nat nat}.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier (reify_prng Rng) rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R} `{!SubOfe locO R} `{!SubOfe unitO R} .
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!prngG Σ, !gitreeGS_gen rs R Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).
  Variable s : stuckness.

  Notation wp_wand := (wp_wand rs).
  Notation wp_bind := (wp_bind rs).
  Notation wp_new := (wp_new_state rs).
  Notation wp_seed := (wp_seed_state rs).
  Notation wp_gen := (wp_gen_state rs).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).
  Canonical Structure stateO := prng.stateO.

  (* (state, gitree program) steps to (post-state, gitree value)
     implies
     (state, PL program) steps (post-state, PL value)
     such that the gitree values is related to the PL value *)
  Definition expr_rel {S} (Φ : ITV → val S → iProp) (α : IT) (e : expr S) : iProp :=
    ∀ (σ : prng.state), has_substate σ -∗ has_prngs σ -∗
        WP@{rs} α @ s {{ βv, ∃ m v σ', ⌜prim_steps e σ (Val v) σ' m⌝
                            ∗ has_substate σ'
                            ∗ has_prngs σ'
                            ∗ Φ βv v }}.

  #[export] Instance expr_rel_ne {S} (V : ITV → val S → iProp) :
    NonExpansive2 V → NonExpansive2 (expr_rel V).
  Proof.
    unfold expr_rel.
    intros ????????.
    f_equiv.
    intros ?; simpl.
    f_equiv.
    f_equiv.
    f_equiv; first done.
    intros ?; simpl.
    f_equiv.
    intros ?; simpl.
    solve_proper.
  Qed.

  Lemma rel_ret_val {S} α αv (v : val S) Φ `{!IntoVal α αv} :
    Φ αv v ⊢ expr_rel Φ α v.
  Proof.
    iIntros "H %σ Hs Hp".
    iApply wp_val; iModIntro.
    iExists (0,0), v, σ.
    iFrame.
    iPureIntro.
    constructor.
  Qed.

  Definition val_nat {S} (αv : ITV) (vn : val S) : iProp :=
    ∃ (n : nat), αv ≡ RetV n ∧ vn ≡ LitV n.
  Definition val_unit {S} (αv : ITV) (vu : val S) : iProp :=
    αv ≡ RetV () ∧ vu ≡ UnitV.
  Definition val_prng {S} (αv : ITV) (vp : val S) : iProp :=
    ∃ (l : loc), αv ≡ RetV l ∗ vp ≡ LitPrng l ∗ known_prng l.
  Definition val_func {S} (Φ1 Φ2 : ITV → val S → iProp) (αv : ITV) (vf : val S) : iProp :=
    ∃ f, IT_of_V αv ≡ Fun f
       ∧ □ ∀ (βv : ITV) (xv : val S),
              Φ1 βv xv -∗ expr_rel Φ2
                            (Fun f ⊙ (IT_of_V βv))
                            (App (Val vf) (Val xv)).

  Fixpoint val_rel (τ : ty) {S} : ITV → val S → iProp :=
    match τ with
    | Tunit => val_unit
    | Tnat => val_nat
    | Tprng => val_prng
    | Tarr τ1 τ2 => val_func (val_rel τ1) (val_rel τ2)
    end.

  Definition logrel (τ : ty) {S} := expr_rel (val_rel τ (S:=S)).

  #[global] Instance prng_lang_val_rel_persist' τ {S} v_git v_pl : Persistent (val_rel τ v_git v_pl (S:=S)).
  Proof. induction τ; apply _. Qed.

  #[export] Program Instance prng_adequacy_val_nat_ne {S} : NonExpansive2 (@val_nat S).
  #[export] Program Instance prng_adequacy_val_unit_ne {S} : NonExpansive2 (@val_unit S).
  #[export] Program Instance prng_adequacy_val_prng_ne {S} : NonExpansive2 (@val_prng S).
  #[export] Program Instance prng_adequacy_val_func_ne {S} Vdom Vcodom
    : NonExpansive2 Vdom → NonExpansive2 Vcodom → NonExpansive2 (@val_func S Vdom Vcodom).
  #[export] Program Instance prng_adequacy_val_nat_proper {S} : Proper ((≡) ==> (≡) ==> (≡)) (@val_nat S).
  #[export] Program Instance prng_adequacy_val_unit_proper {S} : Proper ((≡) ==> (≡) ==> (≡)) (@val_unit S).
  #[export] Program Instance prng_adequacy_val_prng_proper {S} : Proper ((≡) ==> (≡) ==> (≡)) (@val_prng S).
  #[export] Program Instance prng_adequacy_val_func_proper {S} Vdom Vcodom :
    Proper ((≡) ==> (≡) ==> (≡)) Vdom →
    Proper ((≡) ==> (≡) ==> (≡)) Vcodom →
    Proper ((≡) ==> (≡) ==> (≡)) (@val_func S Vdom Vcodom).
  #[export] Program Instance prng_adequacy_expr_rel_proper {S} (V : ITV → val S → iProp) :
    Proper ((≡) ==> (≡) ==> (≡)) V →
    Proper ((≡) ==> (≡) ==> (≡)) (expr_rel V).

  Solve All Obligations with solve_proper.

  #[export] Instance prng_adequacy_val_rel_ne {S} τ:
    NonExpansive2 (@val_rel τ S).
  Proof. induction τ; simpl; solve_proper. Qed.
  #[export] Instance prng_adequacy_val_rel_proper {S} τ:
    Proper ((≡) ==> (≡) ==> (≡)) (val_rel τ (S:=S)).
  Proof. induction τ; simpl; solve_proper. Qed.
  #[export] Instance prng_adequacy_logrel_proper {S} τ:
    Proper ((≡) ==> (≡) ==> (≡)) (logrel τ (S:=S)).
  Proof. solve_proper. Qed.


  Lemma rel_bind {S} (f : IT → IT) (K : ectx S) Ψ Φ `{!NonExpansive2 Φ} `{!IT_hom f} α e :
    ⊢ expr_rel Ψ α e -∗
      (∀ αv v, Ψ αv v -∗
                   expr_rel Φ (f (IT_of_V αv)) (fill K (Val v))) -∗
      expr_rel Φ (f α) (fill K e).
  Proof.
    iIntros "Hrel Hbind".
    iLöb as "IH" forall (α e).
    iIntros (σ) "Hs Hp".
    iApply wp_bind. { solve_proper. }
    iSpecialize ("Hrel" with "Hs Hp").
    iApply (wp_wand with "Hrel").
    iIntros (αv). iDestruct 1 as ([m m'] v σ' Hsteps) "(Hs & Hp & Hrel)".
    apply (prim_steps_ctx K) in Hsteps.
    iSpecialize ("Hbind" with "Hrel Hs Hp").
    iApply (wp_wand with "Hbind"). iModIntro.
    iIntros (βv). iDestruct 1 as ([m2 m2'] v2 σ2' Hsteps2) "[H2 Hs]".
    iExists (m + m2, m' + m2'),v2,σ2'. iFrame "H2 Hs".
    iPureIntro. eapply (prim_steps_app (m,m') (m2,m2')); eauto.
  Qed.

  (* subject expansion, on PL expression side *)
  Lemma rel_pure_expansion {S} (e e' : expr S) n Φ `{!NonExpansive2 Φ} α :
    (∀ σ, prim_step e σ e' σ (n, 0)) →
    ⊢ expr_rel Φ α e' -∗ expr_rel Φ α e.
  Proof.
    intros Hsteps.
    iIntros "Hrel %σ Hs Hp".
    specialize (Hsteps σ).
    iSpecialize ("Hrel" $! σ with "Hs Hp").
    iApply (wp_wand with "Hrel").
    iIntros (αv) "H".
    iDestruct "H" as ([m1 m2] v σ' Hsteps') "[Hs Hp]".
    iModIntro.
    iExists (n+m1,m2), v, σ'.
    iFrame.
    iPureIntro.
    eapply (prim_steps_app (n,0) (m1,m2)); eauto.
    eapply prim_step_steps; eauto.
  Qed.


  (* Context Γ, gitree values indexed Γ, cloesd program values indexed by Γ.
     gitree i ~(Γ i)~ program_value i *)
  Definition env_valid {S : Set}
    (Γ : S -> ty)
    (tvs : interp_scope S)
    (evs : S [⇒] Empty_set) : iProp :=
    (∀ x, □ logrel (Γ x) (tvs x) (evs x))%I.

  Definition valid1 {S : Set} (Γ : S → ty) (α : interp_scope S -n> IT) (e : expr S) (τ : ty) : iProp :=
    ∀ tvs evs, env_valid Γ tvs evs -∗ logrel τ (α tvs) (bind evs e).


  Lemma compat_unit {S : Set} (Γ : S → ty) :
    ⊢ valid1 Γ (interp_unit rs) (Val UnitV) Tunit.
  Proof.
    iIntros (tvs evs) "#Henv".
    by iApply rel_ret_val.
  Qed.

  Lemma compat_nat {S : Set} (Γ : S → ty) (n : nat) :
    ⊢ valid1 Γ (interp_nat rs n) (LitV n) Tnat.
  Proof.
    iIntros (tvs evs) "#Henv".
    iApply rel_ret_val.
    by iExists n.
  Qed.

  Lemma compat_var {S : Set} (Γ : S → ty) (x : S) :
    ⊢ valid1 Γ (interp_var x) (Var x) (Γ x).
  Proof.
    iIntros (tvs evs) "#Henv".
    iApply "Henv".
  Qed.

  Lemma compat_if {S : Set} (Γ : S → ty) τ α β1 β2 a b1 b2:
    ⊢ valid1 Γ α a Tnat -∗
      valid1 Γ β1 b1 τ -∗
      valid1 Γ β2 b2 τ -∗
      valid1 Γ (interp_if rs α β1 β2) (if a then b1 else b2)%syn τ.
  Proof.
    iIntros "H0 H1 H2".
    iIntros (tvs evs) "#Henv".
    iSpecialize ("H0" $! tvs evs with "Henv");
    iSpecialize ("H1" $! tvs evs with "Henv");
    iSpecialize ("H2" $! tvs evs with "Henv").
    iApply (rel_bind (IFSCtx (β1 tvs) (β2 tvs)) (bind evs $ IfK EmptyK b1 b2) (val_rel Tnat) with "H0").
    iIntros (αv v) "(%n & HeqIT & HeqEV)".
    iRewrite "HeqIT"; iRewrite "HeqEV".
    rewrite /IFSCtx IT_of_V_Ret.
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply (rel_pure_expansion _ (bind evs b2) 0 with "H2").
      intros ?. apply (Ectx_step' EmptyK).
      econstructor; eauto.
    - rewrite IF_True; last lia.
      iApply (rel_pure_expansion _ (bind evs b1) 0 with "H1").
      intros ?. apply (Ectx_step' EmptyK).
      econstructor; eauto.
      lia.
  Qed.

  (* [typed_NewPrng] *)
  Lemma compat_NewPrng {S : Set} {Γ : S → ty} :
    ⊢ valid1 Γ (interp_new rs) NewPrng Tprng.
  Proof.
    iIntros (tvs evs) "#Henv".
    iIntros (σ) "Hs Hp /=".
    iApply (wp_new with "Hs Hp"). { solve_proper. }
    iIntros "!>!> Hs Hp Hl".
    iApply wp_val.
    iModIntro.
    iExists (1,1),(LitPrng $ Loc.fresh $ dom σ),_.
    iFrame.
    iSplit; last done.
    iPureIntro.
    apply prim_step_steps.
    apply (Ectx_step' EmptyK).
    by constructor.
  Qed.

  (* [typed_Rand] *)
  Lemma compat_Rand {S : Set} {Γ : S → ty} α e :
    ⊢ valid1 Γ α e Tprng -∗
      valid1 Γ (interp_rand rs α) (Rand e) Tnat.
  Proof.
    iIntros "H".
    iIntros (tvs evs) "#Henv".
    iIntros (σ) "Hs Hp /=".
    iSpecialize ("H" $! tvs evs with "Henv").
    iApply (rel_bind (λ l, get_ret PRNG_GEN l) (bind evs $ RandK EmptyK) (val_rel Tprng) with "H [] Hs Hp").
    iIntros (αlv lv) "Hrel".
    iDestruct "Hrel" as (l) "(Heq & -> & Hl)".
    iRewrite "Heq".
    iSimpl.
    (* XXX: this definitional unfold is for typeclass resolution ... *)
    change (val_nat) with (val_rel Tnat (S:=Empty_set)).
    rewrite IT_of_V_Ret get_ret_ret.
    iIntros (σ0) "Hs Hp".
    iPoseProof (istate_read l with "Hp Hl") as "(%n & %Hlk)".
    iApply (wp_gen l n with "Hs Hp Hl"); first done.
    iIntros "!>!> Hs Hp Hl".
    iExists (1,1),(LitV $ read_out n),_.
    iFrame.
    iSplit; last by iExists _.
    iPureIntro.
    apply prim_step_steps.
    apply (Ectx_step' EmptyK).
    constructor.
    rewrite /state_gen Hlk //.
  Qed.

  (* [typed_Seed] *)
  Lemma compat_Seed {S : Set} {Γ : S → ty} α β el es :
    ⊢ valid1 Γ α el Tprng -∗
      valid1 Γ β es Tnat -∗
      valid1 Γ (interp_seed rs α β) (Seed el es) Tunit.
  Proof.
    iIntros "H1 H2".
    iIntros (tvs evs) "#Henv".
    iIntros (σ) "Hs Hp /=".
    iSpecialize ("H1" $! tvs evs with "Henv").
    iApply (rel_bind (SeedGitCtxL rs (β tvs)) (bind evs $ SeedKl EmptyK es) (val_rel Tprng) with "H1 [H2] Hs Hp").
    iIntros (αlv lv) "(%l & Heq & -> & Hl)".
    iRewrite "Heq"; iSimpl.
    iIntros (σ0) "Hs Hp /=".
    iSpecialize ("H2" $! tvs evs with "Henv").
    iApply (rel_bind (SeedGitCtxS rs (IT_of_V (RetV l))) (bind evs $ SeedKs (LitPrng l) EmptyK) (val_rel Tnat) with "H2 [Hl] Hs Hp").
    iIntros (αsv sv) "(%m & Heq & ->)".
    iRewrite "Heq"; iSimpl.
    (* XXX: this definitional unfold is for typeclass resolution ... *)
    change (val_unit) with (val_rel Tunit (S:=Empty_set)).
    rewrite /SeedGitCtxS !IT_of_V_Ret SeedGit_Ret.
    iIntros (σ1) "Hs Hp".
    iPoseProof (istate_read l with "Hp Hl") as "(%n & %Hlk)".
    iApply (wp_seed l n with "Hs Hp Hl"); first done.
    iIntros "!>!> Hs Hp Hl".
    iExists (1,1),UnitV,_.
    iFrame.
    iSplit; last done.
    iPureIntro.
    apply prim_step_steps.
    apply (Ectx_step' EmptyK).
    constructor.
    rewrite /state_seed Hlk //.
  Qed.

  Lemma compat_app {S : Set} (Γ : S → ty) φ υ f u τ1 τ2 :
    ⊢ valid1 Γ φ f (Tarr τ1 τ2) -∗
      valid1 Γ υ u τ1 -∗
      valid1 Γ (interp_app rs φ υ) (App f u) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (tvs evs) "#Henv".
    iIntros (σ) "Hs Hp".
    iSpecialize ("H2" $! tvs evs with "Henv").
    iApply (rel_bind (AppRSCtx (φ tvs)) (AppRK (bind evs f) EmptyK) (val_rel τ1) with "H2 [H1] Hs Hp").
    iIntros (υv uv) "H2".
    iIntros (σ0) "Hs Hp".
    iSpecialize ("H1" $! tvs evs with "Henv").
    iApply (rel_bind (AppLSCtx (IT_of_V υv)) (AppLK EmptyK uv) (val_rel (Tarr τ1 τ2)) with "H1 [H2] Hs Hp").
    iIntros (φv fv) "(%φ' & Heq & H1)".
    fold val_rel.
    iRewrite "Heq".
    iApply ("H1" with "H2").
  Qed.

  Lemma compat_rec {S : Set} (Γ : S → ty) τ1 τ2 α e :
    ⊢ □ valid1 (Γ ▹ (Tarr τ1 τ2) ▹ τ1) α e τ2 -∗
      valid1 Γ (interp_rec rs α) (Val $ RecV e) (Tarr τ1 τ2).
  Proof.
    iIntros "#H".
    iIntros (tvs evs) "#Henv".
    rewrite interp_rec_unfold.
    iApply rel_ret_val.
    fold @ebind.
    iExists _.
    fold val_rel.
    iSplit; first done.
    iLöb as "IH".
    iModIntro.
    iIntros (βv bv) "#H1".
    rewrite APP_APP'_ITV APP_Fun laterO_map_Next -Tick_eq.
    set (tvs' := (extend_scope (extend_scope tvs (interp_rec rs α tvs)) (IT_of_V βv))).
    set (evs' := ((mk_subst (Val (rec bind ((evs ↑) ↑)%bind e)%syn))
                   ∘ ((mk_subst (shift (Val bv))) ∘ ((evs ↑) ↑)))%bind).
    iApply (rel_pure_expansion _ ((bind evs' e)%syn) 1).
    {
      intros ?.
      eapply (Ectx_step' EmptyK).
      term_simpl.
      rewrite -!bind_bind_comp'.
      apply BetaS.
    }
    iIntros (σ) "Hs Hp".
    iApply wp_tick. iNext. iIntros "Hlc".
    iAssert (env_valid (Γ ▹ (τ1 →ₜ τ2)%typ ▹ τ1) tvs' evs') as "Henv'".
    {
      rewrite /evs' /tvs'.
      iIntros (x'); destruct x' as [| [| x']]; term_simpl; iModIntro.
      { (* ext 0 *)
        iApply (rel_ret_val with "H1").
      }
      { (* ext 1 *)
        iApply rel_ret_val.
        {
          rewrite interp_rec_unfold.
          apply intoval_fun.
        }
        iExists (Next (ir_unf rs α tvs)).
        fold @val_rel.
        iSplit; first done.
        iApply "IH".
      }
      { (* index in env. already known related *)
        iApply "Henv".
      }
    }
    iApply ("H" with "Henv' Hs Hp").
  Qed.

  Lemma compat_natop {S : Set} (Γ : S → ty) op α1 α2 e1 e2 :
    ⊢ valid1 Γ α1 e1 Tnat -∗
      valid1 Γ α2 e2 Tnat -∗
      valid1 Γ (interp_natop _ op α1 α2) (NatOp op e1 e2) Tnat.
  Proof.
    iIntros "H1 H2".
    iIntros (tvs evs) "#Henv".
    iIntros (σ) "Hs Hp /=".
    iSpecialize ("H2" $! tvs evs with "Henv").
    iApply (rel_bind (NatOpRSCtx (do_natop op) (α1 tvs)) (NatOpRK op (bind evs e1) EmptyK) (val_rel Tnat) with "H2 [H1] Hs Hp").
    iIntros (β2 v2) "(%n2 & Ht2 & ->)".
    iRewrite "Ht2".
    change (val_nat) with (val_rel Tnat (S:=Empty_set)).
    rewrite IT_of_V_Ret.
    iIntros (σ1) "Hs Hp /=".
    iSpecialize ("H1" $! tvs evs with "Henv").
    iApply (rel_bind (NatOpLSCtx (do_natop op) (Ret n2)) (NatOpLK op EmptyK (LitV n2)) with "H1 [] Hs Hp").
    iIntros (β1 v1) "(%n1 & Ht1 & ->)".
    iRewrite "Ht1".
    change (val_nat) with (val_rel Tnat (S:=Empty_set)).
    rewrite /NatOpLSCtx IT_of_V_Ret NATOP_Ret /=.
    iApply (rel_pure_expansion _ (LitV $ do_natop op n1 n2) 0).
    {
      intros ?. apply (Ectx_step' EmptyK).
      by constructor.
    }
    by iApply compat_nat.
  Qed.

  Lemma fundamental {S : Set} (Γ : S → ty) e τ :
    typed Γ e τ → ⊢ valid1 Γ (interp_expr rs e) e τ
  with fundamental_val {S : Set} (Γ : S → ty) v τ :
    typed_val Γ v τ → ⊢ valid1 Γ (interp_val rs v) v τ.
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
    ⊢ valid1 □ (interp_expr rs e) e τ.
  Proof. apply fundamental. Qed.
End prng_logrel.

Section reduction_correspondence_adeqaucy.

Context {Rng : Prng nat nat}.
Notation reify_prng := (reify_prng Rng).

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

Let R := sumO natO (sumO unitO locO).
Let sRef := gReifiers_sReifier rs.
Let sOps := sReifier_ops sRef.
Let IT := IT sOps R.
Let ITV := ITV sOps R.
Let fullState := sReifier_state sRef ♯ IT.

Definition κ {S} : ITV → val S :=  λ x,
    match x with
    | core.RetV v => match v with 
                     | inl n => LitV n
                     | inr (inl ()) => UnitV
                     | inr (inr l) => LitPrng l
                     end
    | _ => LitV 0
    end.
Lemma κ_Ret {S} n : κ ((RetV n) : ITV) = (LitV n : val S).
Proof.
  Transparent RetV. unfold RetV. simpl. done. Opaque RetV.
Qed.

Lemma logrel_nat_adequacy  Σ `{!invGpreS Σ}`{!statePreG rs R Σ} `{!prngPreG Σ} {S}
  (α : IT) (e : expr S) n (σ : prng.state) (σ' : fullState) k :
  (∀ `{H1 : !gitreeGS_gen rs R Σ} `{H2 : !prngG Σ},
      (True ⊢ logrel rs notStuck Tnat α e)%I) →
  external_steps sRef α (σ,()) (Ret n) σ' [] k →
  ∃ m σ', prim_steps e σ (Val $ LitV n) σ' m.
Proof.
  intros Hlog Hst.
  pose (ϕ := λ (βv : ITV), ∃ m σ', prim_steps e σ (Val $ κ βv) σ' m).
  cut (ϕ (RetV n)).
  {
    destruct 1 as ( m' & σ2 & Hm).
    exists m', σ2. revert Hm. by rewrite κ_Ret.
  }

  eapply (wp_adequacy 0 (λ x, x) 1 NotCtxDep rs Σ α (σ,()) (Ret n) σ' notStuck k).

  intros Hinv1 Hst1.
  pose H3 : gitreeGS_gen rs R Σ := PrngLangGitreeGS rs Σ Hinv1 Hst1.
  simpl in H3.
  iExists (@state_interp_fun _ _ rs _ _ _ H3).
  iExists (@aux_interp_fun _ _ rs _ _ _ H3).
  iExists (@fork_post _ _ rs _ _ _ H3).
  iExists (@fork_post_ne _ _ rs _ _ _ H3).
  iMod (new_prngG σ) as (H4) "Hprng".
  pose (Φ := (λ (βv : ITV), ∃ n, val_rel rs notStuck Tnat (Σ:=Σ) (S:=S) βv (LitV n)
          ∗ ⌜∃ m σ', prim_steps e σ (Val $ LitV n) σ' m⌝)%I).
  assert (NonExpansive Φ).
  {
    unfold Φ.
    intros l a1 a2 Ha. repeat f_equiv. done.
  }
  iExists Φ, _.
  iExists (@state_interp_fun_mono _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_ne _ _ rs _ _ _ H3).
  iExists (@state_interp_fun_decomp _ _ rs _ _ _ H3).  
  simpl.
  iPoseProof (external_steps_internal_steps _ _ _ _ _ _ _ Hst) as "J1".
  iFrame "J1"; iClear "J1".
  iAssert (True%I) as "G"; first done; iFrame "G"; iClear "G".
  iModIntro.
  iSplitL "Hprng".
  - iIntros "(_ & Hst)".
    iPoseProof (Hlog _ with "[//]") as "Hlog".
    iAssert (has_substate (σ : oFunctor_car (sReifier_state reify_prng) IT IT)) with "[Hst]" as "Hst".
    {
      unfold has_substate, has_full_state.
      fold sRef sOps IT.
      assert (of_state rs IT (σ, ()) ≡ of_idx rs IT 0 σ)%stdpp as ->; last done.
      intro j. unfold sR_idx. simpl.
      unfold of_state, of_idx.
      destruct decide as [Heq|]; last first.
      { inv_fin j; first done.
        intros i. inversion i. }
      inv_fin j; last done.
      intros Heq.
      rewrite (eq_pi _ _ Heq eq_refl)//.
    }
    iSpecialize ("Hlog" $! σ with "Hst Hprng").
    iApply (wp_wand with "Hlog").
    iIntros ( βv). iIntros "H".
    iDestruct "H" as (m' v σ1' Hsts) "(Hst & Hprng & Hrel)".
    unfold Φ. iDestruct "Hrel" as (n0) "[Hβ %]". simplify_eq/=.
    iExists n0. iModIntro. iSplit; eauto.
    iExists n0. iSplit; eauto.
  - iIntros "Hst HΦ Hstuck".
    iAssert ((IT_to_V (Ret n)) ≡ Some (RetV n))%I as "HEQ".
    { by rewrite IT_to_V_Ret. }
    iDestruct (internal_eq_rewrite _ _
                 (λ x, from_option Φ True%I x)
                with "HEQ HΦ")
      as "HΦ".
    { solve_proper. }
    iClear "HEQ".
    iSimpl in "HΦ".
    iDestruct "HΦ" as (n') "[(%p & J1 & %J2) %J3]".
    rewrite J2 in J3; clear J2.
    iEval (subst ϕ; simpl).
    rewrite κ_Ret.
    iPoseProof (RetV_inj with "J1") as "->".
    iApply fupd_mask_intro; first done.
    iIntros "H".
    by iPureIntro.
Qed.

Theorem prng_adequacy_nat (e : expr ∅) (k : nat) σ σ' n :
  typed □ e Tnat →
  external_steps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) (σ,()) (Ret k : IT) σ' [] n →
  ∃ mm σ', prim_steps e σ (Val $ LitV k) σ' mm.
Proof.
  intros Htyped Hsteps.
  pose (Σ:=#[invΣ;stateΣ rs R;prngΣ]).
  eapply (logrel_nat_adequacy Σ (interp_expr rs e ı_scope)); last eassumption.
  intros ? ?.
  iIntros "_".
  iPoseProof (fundamental rs notStuck □ e Tnat Htyped) as "H".
  iSpecialize ("H" $! ı_scope ı%bind with "[]").
  { iIntros (x); destruct x. }
  rewrite ebind_id; last done.
  iApply "H".
Qed.

End reduction_correspondence_adeqaucy.


