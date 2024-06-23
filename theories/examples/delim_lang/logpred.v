From gitrees Require Import gitree lang_generic hom.
From gitrees.effects Require Import delim.
From gitrees.examples.delim_lang Require Import lang interp typing hom.
From iris.algebra Require Import list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.

Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope stdpp_scope.

Section logrel.
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!subReifier reify_delim rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ}.
  Context `{!stateG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation restO
    := (gState_rest
          (@sR_idx _ _
             (sReifier_NotCtxDep_CtxDep reify_delim)) rs ♯ IT).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).
  Canonical Structure contO S := leibnizO (cont S).
  Canonical Structure mcontO S := leibnizO (Mcont S).

  Notation "'WP' α {{ β , Φ } }"
    := (wp rs α notStuck ⊤ (λ β, Φ))
         (at level 20, α, Φ at level 200,
           format "'WP'  α  {{  β ,  Φ  } }")
      : bi_scope.

  Notation "'WP' α {{ Φ } }"
    := (wp rs α notStuck ⊤ Φ)
         (at level 20, α, Φ at level 200,
           format "'WP'  α  {{  Φ  } }") : bi_scope.

  Definition logrel_nat' (βv : ITV) : iProp :=
    (∃ (n : natO), βv ≡ RetV n)%I.
  Local Instance logrel_nat_ne : NonExpansive logrel_nat'.
  Proof. solve_proper. Qed.
  Definition logrel_nat : ITV -n> iProp := λne x, logrel_nat' x.

  Definition obs_ref'
    (t : IT) (κ : HOM) (σ : stateF ♯ IT)
    : iProp :=
    (has_substate σ -∗ WP (𝒫 (`κ t)) {{ βv, has_substate [] }})%I.
  Local Instance obs_ref_ne : NonExpansive3 obs_ref'.
  Proof. solve_proper. Qed.
  Program Definition obs_ref : IT -n> HOM -n> (stateF ♯ IT) -n> iProp :=
    λne x y z, obs_ref' x y z.
  Solve All Obligations with solve_proper.

  Definition logrel_mcont' (P : ITV -n> iProp) (F : stateF ♯ IT) :=
    (∀ αv, P αv -∗ obs_ref (IT_of_V αv) HOM_id F)%I.
  Local Instance logrel_mcont_ne : NonExpansive2 logrel_mcont'.
  Proof. solve_proper. Qed.
  Program Definition logrel_mcont : (ITV -n> iProp) -n> (stateF ♯ IT) -n> iProp
    := λne x y, logrel_mcont' x y.
  Solve All Obligations with solve_proper.

  Program Definition logrel_ectx'
    (Pτ Pα : ITV -n> iProp) (κ : HOM)
    : iProp :=
    (□ ∀ αv, Pτ αv -∗ ∀ σ, logrel_mcont Pα σ -∗ obs_ref (IT_of_V αv) κ σ)%I.
  Local Instance logrel_ectx_ne : NonExpansive3 logrel_ectx'.
  Proof. solve_proper. Qed.
  Program Definition logrel_ectx
    : (ITV -n> iProp) -n> (ITV -n> iProp) -n> HOM -n> iProp
    := λne x y z, logrel_ectx' x y z.
  Solve All Obligations with solve_proper.

  Program Definition logrel_cont' V W (βv : ITV) : iProp :=
    (∃ (κ : HOM), (IT_of_V βv) ≡
                    (Fun (Next (λne x, Tau (laterO_map (𝒫 ◎ `κ) (Next x)))))
                  ∧ □ logrel_ectx V W κ)%I.
  Local Instance logrel_cont_ne : NonExpansive3 logrel_cont'.
  Proof. solve_proper. Qed.
  Program Definition logrel_cont
    : (ITV -n> iProp) -n> (ITV -n> iProp) -n> ITV -n> iProp
    := λne x y z, logrel_cont' x y z.
  Solve All Obligations with solve_proper.

  Program Definition logrel_arr' (Pτ Pα Pσ Pβ : ITV -n> iProp) (f : ITV) : iProp
    := (∃ f', IT_of_V f ≡ Fun f'
              ∧ □ ∀ (βv : ITV),
          Pτ βv -∗ ∀ (κ : HOM),
          logrel_ectx Pσ Pα κ -∗ ∀ σ,
          logrel_mcont Pβ σ -∗ obs_ref (APP' (Fun f') (IT_of_V βv)) κ σ)%I.
  Local Instance logrel_arr_ne
    : (∀ n, Proper (dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n)
              logrel_arr').
  Proof. solve_proper. Qed.
  Program Definition logrel_arr
    : (ITV -n> iProp)
      -n> (ITV -n> iProp)
          -n> (ITV -n> iProp)
              -n> (ITV -n> iProp) -n> ITV -n> iProp :=
    λne x y z w v, logrel_arr' x y z w v.
  Solve All Obligations with solve_proper.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tnat => logrel_nat
    | Tcont α β => logrel_cont (interp_ty α) (interp_ty β)
    | Tarr τ α σ β => logrel_arr (interp_ty τ) (interp_ty α)
                       (interp_ty σ) (interp_ty β)
    end.

  Local Instance interp_ty_persistent (τ : ty) α :
    Persistent (interp_ty τ α).
  Proof.
    revert α. induction τ=> α; simpl.
    - unfold logrel_nat. apply _.
    - unfold logrel_arr. apply _.
    - unfold logrel_cont. apply _.
  Qed.

  Program Definition logrel_expr (τ α δ : ITV -n> iProp) : IT -n> iProp
    := λne e, (∀ E, logrel_ectx τ α E
                    -∗ ∀ F, logrel_mcont δ F
                            -∗ obs_ref e E F)%I.
  Solve All Obligations with solve_proper.

  Definition logrel (τ α β : ty) : IT -n> iProp
    := logrel_expr (interp_ty τ) (interp_ty α) (interp_ty β).

  Program Definition ssubst_valid {S : Set}
    (Γ : S -> ty)
    (ss : interp_scope S) : iProp :=
    (∀ x τ, □ logrel (Γ x) τ τ (ss x))%I.

  Program Definition valid {S : Set}
    (Γ : S -> ty)
    (e : interp_scope S -n> IT)
    (τ α σ : ty) : iProp :=
    (□ ∀ γ, ssubst_valid Γ γ
          -∗ logrel τ α σ (e γ))%I.

  Lemma compat_HOM_id P :
    ⊢ logrel_ectx P P HOM_id.
  Proof.
    iIntros (v).
    iModIntro.
    iIntros "Pv".
    iIntros (σ) "Hσ HH".
    iApply ("Hσ" with "Pv HH").
  Qed.

  Lemma logrel_of_val τ α v :
    interp_ty α v -∗ logrel α τ τ (IT_of_V v).
  Proof.
    iIntros "#H".
    iIntros (κ) "Hκ".
    iIntros (σ) "Hσ Hown".
    iApply ("Hκ" with "H Hσ Hown").
  Qed.

  Lemma compat_var {S : Set} (Γ : S -> ty) (x : S) :
    ⊢ (∀ α, valid Γ (interp_var x) (Γ x) α α).
  Proof.
    iIntros (α).
    iModIntro.
    iIntros (γ) "#Hss".
    iIntros (E) "HE".
    iIntros (F) "HF".
    iIntros "Hσ".
    iApply ("Hss" with "HE HF Hσ").
  Qed.

  Lemma compat_reset {S : Set} (Γ : S -> ty) e σ τ :
    ⊢ valid Γ e σ σ τ -∗ (∀ α, valid Γ (interp_reset rs e) τ α α).
  Proof.
    iIntros "#H".
    iIntros (α).
    iModIntro.
    iIntros (γ) "Hγ".
    iIntros (κ) "Hκ".
    iIntros (m) "Hm Hst".
    assert (𝒫 ((`κ) (interp_reset rs e γ))
              ≡ (𝒫 ◎ `κ) (interp_reset rs e γ)) as ->.
    { reflexivity. }
    iApply (wp_reset with "Hst").
    iNext.
    iIntros "_ Hst".
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! HOM_id (compat_HOM_id _) (laterO_map (𝒫 ◎ `κ) :: m)).
    iAssert (logrel_mcont (interp_ty τ) (laterO_map (𝒫 ◎ `κ) :: m))
      with "[Hm Hκ]" as "Hm".
    {
      iIntros (v) "Hv Hst".
      iApply (wp_pop_cons with "Hst").
      iNext.
      iIntros "_ Hst".
      iSpecialize ("Hκ" $! v with "Hv").
      iSpecialize ("Hκ" $! m with "Hm").
      iSpecialize ("Hκ" with "Hst").
      iApply "Hκ".
    }
    iSpecialize ("H" with "Hm Hst").
    iApply "H".
  Qed.

  Lemma compat_shift {S : Set} (Γ : S -> ty) e σ α τ β :
    ⊢ valid (Γ ▹ (Tcont τ α)) e σ σ β -∗ valid Γ (interp_shift _ e) τ α β.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ) "#Hκ".
    iIntros (m) "Hm Hst".
    assert (𝒫 ((`κ) (interp_shift rs e γ))
              ≡ (𝒫 ◎ `κ) (interp_shift rs e γ)) as ->.
    { reflexivity. }
    iApply (wp_shift with "Hst").
    { rewrite laterO_map_Next; reflexivity. }
    iNext.
    iIntros "_ Hst".
    match goal with
    | |- context G [ofe_mor_car _ _ e ?a] =>
        set (γ' := a)
    end.
    iAssert (ssubst_valid (Γ ▹ Tcont τ α) γ') with "[Hγ Hκ]" as "Hγ'".
    {
      iIntros (x τ').
      destruct x as [| x].
      - iModIntro.
        subst γ'.
        iIntros (E) "HE".
        iIntros (F) "HF Hst".
        simpl.
        match goal with
        | |- context G [ofe_mor_car _ _ (`E) (ofe_mor_car _ _ Fun ?a)] =>
            set (f := a)
        end.
        iApply ("HE" $! (FunV f) with "[Hκ] HF Hst").
        iExists κ.
        iSplit.
        + subst f; iPureIntro.
          reflexivity.
        + iApply "Hκ".
      - iApply "Hγ".
    }
    iSpecialize ("H" $! γ' with "Hγ'").
    iSpecialize ("H" $! HOM_id (compat_HOM_id _) m with "Hm Hst").
    iApply "H".
  Qed.

  Lemma compat_nat {S : Set} (Γ : S → ty) n α :
    ⊢ valid Γ (interp_nat rs n) Tnat α α.
  Proof.
    iModIntro.
    iIntros (γ) "#Hγ".
    assert ((interp_nat rs n γ) ≡ IT_of_V (RetV n)) as ->.
    { reflexivity. }
    iApply logrel_of_val.
    iExists _; by iPureIntro.
  Qed.

  Lemma compat_recV {S : Set} (Γ : S -> ty)
    τ1 α τ2 β e :
    ⊢ valid ((Γ ▹ (Tarr τ1 α τ2 β) ▹ τ1)) e τ2 α β
      -∗ (∀ θ, valid Γ (interp_rec rs e) (Tarr τ1 α τ2 β) θ θ).
  Proof.
    iIntros "#H".
    iIntros (θ).
    iModIntro.
    iIntros (γ) "#Hγ".
    set (f := (ir_unf rs e γ)).
    iAssert (interp_rec rs e γ ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf".
    Opaque IT_of_V.
    iApply logrel_of_val; term_simpl.
    iExists _. iSplit.
    { iPureIntro. apply into_val. }
    iModIntro.
    iLöb as "IH".
    iIntros (v) "#Hw".
    iIntros (κ) "#Hκ".
    iIntros (σ) "Hσ Hst".
    rewrite APP_APP'_ITV APP_Fun laterO_map_Next -Tick_eq.
    pose (γ' :=
            (extend_scope (extend_scope γ (interp_rec rs e γ)) (IT_of_V v))).
    rewrite /logrel.
    Opaque extend_scope.
    simpl.
    rewrite hom_tick.
    rewrite hom_tick.
    iApply wp_tick.
    iNext.
    iSpecialize ("H" $! γ' with "[Hw]").
    {
      iIntros (x).
      destruct x as [| [| x]]; iIntros (ξ); iModIntro.
      * iApply logrel_of_val.
        iApply "Hw".
      * iIntros (κ') "Hκ'".
        iIntros (σ') "Hσ' Hst".
        Transparent extend_scope.
        simpl.
        iRewrite "Hf".
        iSpecialize ("Hκ'" $! (FunV (Next f)) with "[IH]").
        {
          iExists (Next f).
          iSplit; first done.
          iModIntro.
          iIntros (βv) "Hβv".
          iIntros (κ'') "Hκ''".
          iIntros (σ'') "Hσ'' Hst".
          iApply ("IH" $! βv with "Hβv Hκ'' Hσ'' Hst").
        }
        iApply ("Hκ'" $! σ' with "Hσ' Hst").
      * iApply "Hγ".
    }
    subst γ'.
    iApply ("H" with "Hκ Hσ Hst").
  Qed.

  Lemma compat_nat_op {S : Set} (Γ : S → ty)
    D E F e1 e2 op :
    ⊢ valid Γ e1 Tnat E F
      -∗ valid Γ e2 Tnat F D
      -∗ valid Γ (interp_natop rs op e1 e2) Tnat E D.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ) "#Hκ".
    iIntros (m) "Hm Hst".
    rewrite /interp_natop //=.

    set (κ' := (NatOpRSCtx_HOM op e1 γ)).
    assert ((NATOP (do_natop op) (e1 γ) (e2 γ)) = ((`κ') (e2 γ))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.

    iSpecialize ("G" $! γ with "Hγ").
    iSpecialize ("G" $! sss).
    iApply ("G" with "[H] Hm Hst").

    iIntros (w).
    iModIntro.
    iIntros "#Hw".
    iIntros (m') "Hm Hst".
    subst sss.
    subst κ'.
    simpl.

    pose (κ' := (NatOpLSCtx_HOM op (IT_of_V w) γ _)).
    assert ((NATOP (do_natop op) (e1 γ) (IT_of_V w)) = ((`κ') (e1 γ)))
      as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.

    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! sss).
    iApply ("H" with "[] Hm Hst").

    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (m'') "Hm Hst".
    subst sss.
    subst κ'.
    simpl.

    iDestruct "Hw" as "(%n & #HEQ1)".
    iDestruct "Hv" as "(%n' & #HEQ2)".
    iSpecialize ("Hκ" $! (RetV (do_natop op n' n)) with "[]").
    {
      iExists _.
      iPureIntro.
      reflexivity.
    }
    iSpecialize ("Hκ" $! m'' with "Hm Hst").
    rewrite IT_of_V_Ret.

    iAssert ((NATOP (do_natop op) (IT_of_V v) (IT_of_V w))
               ≡ (Ret (do_natop op n' n)))%I as "#HEQ".
    {
      iRewrite "HEQ1".
      rewrite IT_of_V_Ret.
      iAssert ((IT_of_V v) ≡ IT_of_V (RetV n'))%I as "#HEQ2'".
      {
        iApply f_equivI.
        iApply "HEQ2".
      }
      rewrite IT_of_V_Ret.
      iAssert (NATOP (do_natop op) (IT_of_V v) (Ret n)
                 ≡ NATOP (do_natop op) (Ret n') (Ret n))%I as "#HEQ2''".
      {
        unshelve iApply (f_equivI (λne x, NATOP (do_natop op) x (Ret n))).
        { solve_proper. }
        { solve_proper. }
        iApply "HEQ2'".
      }
      iRewrite "HEQ2''".
      rewrite NATOP_Ret.
      done.
    }
    iRewrite "HEQ".
    iApply "Hκ".
  Qed.

  Lemma compat_app {S : Set} (Γ : S → ty)
    ξ α β δ η τ e1 e2 :
    ⊢ valid Γ e1 (Tarr η α τ β) ξ δ
      -∗ valid Γ e2 η β ξ
      -∗ valid Γ (interp_app rs e1 e2) τ α δ.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ) "#Hκ".
    iIntros (σ) "Hσ Hst".
    rewrite /interp_app //=.

    pose (κ' := (AppLSCtx_HOM e2 γ)).
    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] =>
        set (F := b)
    end.
    assert (LET (e1 γ) F = ((`κ') (e1 γ))) as ->.
    { simpl; unfold AppLSCtx. reflexivity. }
    clear F.
    assert ((`κ) ((`κ') (e1 γ)) = ((`κ) ◎ (`κ')) (e1 γ)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }

    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! sss).
    iApply ("H" with "[H] Hσ Hst").

    iIntros (w).
    iModIntro.
    iIntros "#Hw".
    iIntros (m') "Hm Hst".
    subst sss.
    subst κ'.
    simpl.
    rewrite LET_Val.
    cbn [ofe_mor_car].

    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] =>
        set (F := b)
    end.
    pose (κ'' := exist _ (LETCTX F) (LETCTX_Hom F) : HOM).
    assert (((`κ) (LET (e2 γ) F)) = (((`κ) ◎ (`κ'')) (e2 γ))) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ'')).
    assert ((`κ ◎ `κ'') = (`sss)) as ->.
    { reflexivity. }
    iSpecialize ("G" $! γ with "Hγ").
    iSpecialize ("G" $! sss).
    iApply ("G" with "[H] Hm Hst").
    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (m'') "Hm Hst".
    subst sss.
    subst κ''.
    simpl.
    rewrite LET_Val.
    subst F.
    cbn [ofe_mor_car].

    iDestruct "Hw" as "(%n' & #HEQ & Hw)".
    iSpecialize ("Hw" $! v with "Hv").
    iSpecialize ("Hw" $! κ with "Hκ").
    iSpecialize ("Hw" $! m'' with "Hm Hst").
    iAssert ((IT_of_V w ⊙ (IT_of_V v))
               ≡ (Fun n' ⊙ (IT_of_V v)))%I as "#HEQ'".
    {
      iApply (f_equivI (λne x, (x ⊙ (IT_of_V v)))).
      iApply "HEQ".
    }
    iRewrite "HEQ'".
    iApply "Hw".
  Qed.

  Lemma compat_appcont {S : Set} (Γ : S -> ty) e1 e2 τ α δ β σ :
    valid Γ e1 (Tcont τ α) σ δ
    -∗ valid Γ e2 τ δ β
    -∗ valid Γ (interp_app_cont _ e1 e2) α σ β.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Henv".
    iIntros (κ) "#Hκ".
    iIntros (σ') "Hm Hst".

    pose (κ' := (AppContRSCtx_HOM e1 γ)).
    assert ((interp_app_cont rs e1 e2 γ) = ((`κ') (e2 γ))) as ->.
    { simpl. reflexivity. }
    assert ((`κ) ((`κ') (e2 γ)) = ((`κ) ◎ (`κ')) (e2 γ)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }

    iSpecialize ("G" $! γ with "Henv").
    iSpecialize ("G" $! sss).
    iApply ("G" with "[H] Hm Hst").

    iIntros (w).
    iModIntro.
    iIntros "#Hw".
    iIntros (m') "Hm Hst".
    subst sss.
    subst κ'.
    Opaque interp_app_cont.
    simpl.

    pose (κ'' := (AppContLSCtx_HOM (IT_of_V w) γ _)).
    set (F := (`κ) _).
    assert (F ≡ (((`κ) ◎ (`κ'')) (e1 γ))) as ->.
    {
      subst F. simpl. Transparent interp_app_cont. simpl.
      f_equiv.
      rewrite ->2 get_val_ITV.
      simpl.
      reflexivity.
    }
    pose (sss := (HOM_compose κ κ'')).
    assert ((`κ ◎ `κ'') = (`sss)) as ->.
    { reflexivity. }

    iSpecialize ("H" $! γ with "Henv").
    iSpecialize ("H" $! sss).
    iApply ("H" with "[] Hm Hst").

    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (m'') "Hm Hst".
    subst sss.
    subst κ''.
    Opaque APP_CONT.
    simpl.

    rewrite get_val_ITV.
    simpl.

    iDestruct "Hv" as "(%n' & #HEQ & #Hv)".
    iRewrite "HEQ".
    rewrite get_fun_fun.
    simpl.

    match goal with
    | |- context G [ofe_mor_car _ _
                     (ofe_mor_car _ _ APP_CONT ?a) ?b] =>
        set (T := APP_CONT a b)
    end.
    iAssert (𝒫 ((`κ) T) ≡ (𝒫 ◎ (`κ)) T)%I as "HEQ'".
    { iPureIntro. reflexivity. }
    iRewrite "HEQ'"; iClear "HEQ'".
    subst T.

    iApply (wp_app_cont with "[Hst]").
    { reflexivity. }
    - iFrame "Hst".
    - simpl.
      iNext.
      iIntros "_ Hst".
      rewrite later_map_Next.
      rewrite <-Tick_eq.
      iApply wp_tick.
      iNext.
      iSpecialize ("Hv" $! w with "Hw").

      iApply ("Hv" $! (laterO_map (𝒫 ◎ `κ) :: m'') with "[Hm] Hst").
      {
        iIntros (p) "#Hp Hst".
        iApply (wp_pop_cons with "Hst").
        iNext.
        iIntros "_ Hst".
        iApply ("Hκ" with "Hp Hm Hst").
      }
  Qed.

  Lemma compat_if {S : Set} (Γ : S -> ty) e e₁ e₂ τ σ α β :
        ⊢ valid Γ e Tnat β α
          -∗ valid Γ e₁ τ σ β
          -∗ valid Γ e₂ τ σ β
          -∗ valid Γ (interp_if rs e e₁ e₂) τ σ α.
  Proof.
    iIntros "#H #G #J".
    iModIntro.
    iIntros (γ) "#Henv".
    iIntros (κ) "#Hκ".
    iIntros (σ') "Hm Hst".
    unfold interp_if.
    cbn [ofe_mor_car].
    pose (κ' := (IFSCtx_HOM (e₁ γ) (e₂ γ))).
    assert ((IF (e γ) (e₁ γ) (e₂ γ)) = ((`κ') (e γ))) as -> by reflexivity.
    assert ((`κ) ((`κ') (e γ)) = ((`κ) ◎ (`κ')) (e γ))
      as -> by reflexivity.
    pose (sss := (HOM_compose κ κ')).
    rewrite (HOM_compose_ccompose κ κ' sss)//.

    iSpecialize ("H" $! γ with "Henv").
    iSpecialize ("H" $! sss).
    iApply ("H" with "[] Hm Hst").

    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (σ'') "Hm Hst".
    iDestruct "Hv" as "(%n & #Hv)".
    iRewrite "Hv".
    rewrite IT_of_V_Ret.
    subst sss.
    subst κ'.
    simpl.
    unfold IFSCtx.
    destruct (decide (0 < n)) as [H|H].
    - rewrite IF_True//.
      iApply ("G" $! γ with "Henv [Hκ] Hm Hst").
      iIntros (w).
      iModIntro.
      iIntros "#Hw".
      iIntros (σ''') "Hm Hst".
      iApply ("Hκ" with "Hw Hm Hst").
    - rewrite IF_False//; last lia.
      iApply ("J" $! γ with "Henv [Hκ] Hm Hst").
      iIntros (w).
      iModIntro.
      iIntros "#Hw".
      iIntros (σ''') "Hm Hst".
      iApply ("Hκ" with "Hw Hm Hst").
  Qed.

  Open Scope types.

  Lemma fundamental_expr {S : Set} (Γ : S -> ty) τ α β e :
    Γ; α ⊢ₑ e : τ; β → ⊢ valid Γ (interp_expr rs e) τ α β
  with fundamental_val {S : Set} (Γ : S -> ty) τ α β v :
    Γ; α ⊢ᵥ v : τ; β → ⊢ valid Γ (interp_val rs v) τ α β.
  Proof.
    - intros H.
      destruct H.
      + by apply fundamental_val.
      + subst; iApply compat_var.
      + iApply compat_app;
          by iApply fundamental_expr.
      + iApply compat_appcont;
          by iApply fundamental_expr.
      + iApply compat_nat_op;
          by iApply fundamental_expr.
      + iApply compat_if;
          by iApply fundamental_expr.
      + iApply compat_shift;
          by iApply fundamental_expr.
      + iApply (compat_reset with "[]");
          by iApply fundamental_expr.
    - intros H.
      destruct H.
      + iApply compat_nat.
      + iApply (compat_recV with "[]");
          by iApply fundamental_expr.
  Qed.

End logrel.

Local Definition rs : gReifiers CtxDep 1 := gReifiers_cons reify_delim gReifiers_nil.

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logpred_adequacy cr Σ R `{!Cofe R, SubOfe natO R}
  `{!invGpreS Σ} `{!statePreG rs R Σ} τ
  (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R)
  (e : IT (gReifiers_ops rs) R) st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ},
      (£ cr ⊢ valid rs □ α τ τ τ)%I) →
  ssteps (gReifiers_sReifier rs) (𝒫 (α ı_scope)) ([], ()) e st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) e st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ e).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V e) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) e st' β1 st1)
      ∨ (∃ e', e ≡ Err e' ∧ notStuck e')).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety cr); eauto.
  { apply Hdisj. }
  { by rewrite Hb. }
  intros H1 H2.
  exists (λ _, True)%I. split.
  { apply _. }
  iIntros "[Hcr  Hst]".
  iPoseProof (Hlog with "Hcr") as "Hlog".
  match goal with
  | |- context G [has_full_state (?a, _)] =>
      set (st := a)
  end.
  simpl in st.
  iAssert (has_substate _) with "[Hst]" as "Hs".
  { unfold has_substate, has_full_state.
    eassert (of_state rs (IT (gReifiers_ops rs) _) (_,()) ≡
            of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state _)) as ->; last done.
    intro j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    { inv_fin j; first done.
      intros i. inversion i. }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
    simpl.
    unfold iso_ofe_refl.
    cbn.
    reflexivity.
  }
  iSpecialize ("Hlog" $! ı_scope with "[]").
  { iIntros ([]). }
  iSpecialize ("Hlog" $! HOM_id (compat_HOM_id _ _) [] with "[]").
  {
    iIntros (αv) "HHH GGG".
    iApply (wp_pop_end with "GGG").
    iNext.
    iIntros "_ GGG".
    iApply wp_val.
    by iModIntro.
  }
  subst st.
  iSpecialize ("Hlog" with "Hs").
  iApply (wp_wand with "Hlog").
  iIntros (βv). simpl.
  iIntros "_".
  done.
Qed.
