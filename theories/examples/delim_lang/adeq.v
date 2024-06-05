From gitrees Require Import gitree lang_generic hom.
From gitrees.effects Require Import delim.
From gitrees.examples.delim_lang Require Import lang interp.
From iris.algebra Require Import list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.

(* TODO: typing rules, compat for contexts, binary relation *)

Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope syn.

Inductive ty :=
| Tnat : ty
| Tarr : ty -> ty -> ty -> ty -> ty
| Tcont : ty → ty → ty.

Declare Scope types.

Notation "τ '∕' α '→' σ '∕' β" := (Tarr τ α σ β) (at level 60) : types.
Notation "'Cont' τ σ" := (Tcont τ σ) (at level 60) : types.

Reserved Notation "Γ ';' α '⊢ₑ' e ':' τ ';' β"
  (at level 90, e at next level, τ at level 20, no associativity).

Reserved Notation "Γ ';' α '⊢ᵥ' e ':' τ ';' β"
  (at level 90, e at next level, τ at level 20, no associativity).

Reserved Notation "Γ '⊢ᵪ' e ':' τ '⤞' σ"
  (at level 90, e at next level, τ at level 20, no associativity).

Inductive typed_expr {S : Set} (Γ : S -> ty) : ty -> expr S -> ty -> ty -> Prop :=
| typed_Val v α τ β :
  (Γ; α ⊢ᵥ v : τ; β) →
  (Γ; α ⊢ₑ v : τ; β)
| typed_Var x τ α :
  (Γ x = τ) →
  (Γ; α ⊢ₑ (Var x) : τ; α)
| typed_App e₁ e₂ γ α β δ σ τ :
  (Γ; γ ⊢ₑ e₁ : (Tarr σ α τ β); δ) →
  (Γ; β ⊢ₑ e₂ : σ; γ) →
  (Γ; α ⊢ₑ (App e₁ e₂) : τ; δ)
| typed_AppCont e₁ e₂ α β δ σ τ :
  (Γ; σ ⊢ₑ e₁ : (Tcont τ α); δ) →
  (Γ; δ ⊢ₑ e₂ : τ; β) →
  (Γ; σ ⊢ₑ (AppCont e₁ e₂) : α; β)
| typed_NatOp o e₁ e₂ α β γ :
  (Γ; α ⊢ₑ e₁ : Tnat; β) →
  (Γ; β ⊢ₑ e₂ : Tnat; γ) →
  (Γ; α ⊢ₑ NatOp o e₁ e₂ : Tnat; γ)
| typed_If e e₁ e₂ α β σ τ :
  (Γ; β ⊢ₑ e : Tnat; α) →
  (Γ; σ ⊢ₑ e₁ : τ; β) →
  (Γ; σ ⊢ₑ e₂ : τ; β) →
  (Γ; σ ⊢ₑ (if e then e₁ else e₂) : τ; α)
| typed_Shift (e : @expr (inc S)) τ α σ β :
  (Γ ▹ (Tcont τ α); σ ⊢ₑ e : σ; β) →
  (Γ; α ⊢ₑ Shift e : τ; β)
| typed_Reset e α σ τ :
  (Γ; σ ⊢ₑ e : σ; τ) →
  (Γ; α ⊢ₑ reset e : τ; α)
where "Γ ';' α '⊢ₑ' e ':' τ ';' β" := (typed_expr Γ α e τ β) : types
with typed_val {S : Set} (Γ : S -> ty) : ty -> val S -> ty -> ty -> Prop :=
| typed_LitV n α :
  (Γ; α ⊢ᵥ #n : Tnat; α)
| typed_RecV (e : expr (inc (inc S))) (δ σ τ α β : ty) :
  ((Γ ▹ (Tarr σ α τ β) ▹ σ); α ⊢ₑ e : τ; β) ->
  (Γ; δ ⊢ᵥ (RecV e) : (Tarr σ α τ β); δ)
| typed_ContV (k : cont S) τ σ α :
  (Γ ⊢ᵪ k : τ ⤞ σ) →
  (Γ; α ⊢ᵥ (ContV k) : (Tcont τ σ); α)
where "Γ ';' α '⊢ᵥ' e ':' τ ';' β" := (typed_val Γ α e τ β) : types
with typed_cont {S : Set} (Γ : S -> ty) : cont S -> ty -> ty -> Prop :=
| typed_END τ :
  (Γ ⊢ᵪ END : τ ⤞ τ)
| typed_IfK k e₁ e₂ α β τ :
  (Γ; α ⊢ₑ e₁ : τ; β) ->
  (Γ; α ⊢ₑ e₂ : τ; β) ->
  (Γ ⊢ᵪ k : τ ⤞ α) ->
  (Γ ⊢ᵪ IfK e₁ e₂ k : Tnat ⤞ β)
| typed_NatOpLK op v k α τ :
  (Γ; τ ⊢ᵥ v : Tnat; α) ->
  (Γ ⊢ᵪ k : Tnat ⤞ τ) ->
  (Γ ⊢ᵪ NatOpLK op v k : Tnat ⤞ α)
| typed_NatOpRK op e k α τ :
  (Γ; τ ⊢ₑ e : Tnat; α) ->
  (Γ ⊢ᵪ k : Tnat ⤞ τ) ->
  (Γ ⊢ᵪ NatOpRK op e k : Tnat ⤞ α)
(* (* | typed_AppLK v k α β σ δ τ' τ : *) *)
(* (*   (Γ; α ⊢ᵥ v : τ'; β) -> *) *)
(* (*   (Γ; β ⊢ᵪ k : Tcont σ τ; δ) -> *) *)
(* (*   (Γ; α ⊢ᵪ AppLK v k : Tcont (Tarr τ' α σ δ) τ; δ) *) *)
(* (* | typed_AppRK e k τ : *) *)
(* (*   (Γ; τ ⊢ᵪ AppRK e k : τ; τ) *) *)
(* (* | typed_AppContLK v k τ : *) *)
(* (*   (Γ; τ ⊢ᵪ AppContLK v k : τ; τ) *) *)
(* (* | typed_AppContRK e k τ : *) *)
(* (*   (Γ; τ ⊢ᵪ AppContRK e k : τ; τ) *) *)
where "Γ '⊢ᵪ' e ':' τ '⤞' σ" := (typed_cont Γ e τ σ) : types
.

Module Example.
  Open Scope types.

  Lemma typ_example1 α :
    empty_env; α ⊢ₑ ((#1) +
                          (reset
                             ((#3)
                              + (shift/cc ((($0) @k #5) + (($0) @k #6))))))
    : Tnat; α.
  Proof.
    eapply typed_NatOp.
    - apply typed_Val.
      apply typed_LitV.
    - eapply typed_Reset.
      eapply typed_NatOp.
      + apply typed_Val.
        apply typed_LitV.
      + eapply typed_Shift.
        eapply typed_NatOp.
        * eapply typed_AppCont.
          -- apply typed_Var.
             reflexivity.
          -- apply typed_Val.
             apply typed_LitV.
        * eapply typed_AppCont.
          -- apply typed_Var.
             reflexivity.
          -- apply typed_Val.
             apply typed_LitV.
  Qed.

End Example.

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

  Lemma compat_empty P :
    ⊢ logrel_mcont P [].
  Proof.
    iIntros (v) "Pv HH".
    iApply (wp_pop_end with "HH").
    iNext.
    iIntros "_ HHH".
    by iApply wp_val.
  Qed.

  Lemma compat_cons P Q (x : HOM) (xs : list (later IT -n> later IT)) :
    ⊢ logrel_ectx P Q x
      -∗ logrel_mcont Q xs
      -∗ logrel_mcont P (laterO_map (𝒫 ◎ `x) :: xs).
  Proof.
    iIntros "#H G".
    iIntros (v) "Hv Hst".
    iApply (wp_pop_cons with "Hst").
    iNext.
    iIntros "_ Hst".
    iSpecialize ("H" $! v with "Hv").
    iApply ("H" $! xs with "G Hst").
  Qed.

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

  Program Definition 𝒫_HOM : @HOM sz CtxDep R _ rs := exist _ 𝒫 _.
  Next Obligation.
    apply _.
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

  Program Definition AppContRSCtx_HOM {S : Set}
    (α : @interp_scope F R _ S -n> IT)
    (env : @interp_scope F R _ S)
    : HOM := exist _ (interp_app_contrk rs α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition AppContLSCtx_HOM {S : Set}
    (β : IT) (env : @interp_scope F R _ S)
    (Hv : AsVal β)
    : HOM := exist _ (interp_app_contlk rs (constO β) (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - intros ???.
      do 2 f_equiv.
      intros ?; simpl.
      solve_proper.
    - rewrite get_val_ITV.
      rewrite get_val_ITV.
      simpl.
      rewrite get_fun_tick.
      reflexivity.
    - rewrite get_val_ITV.
      simpl. rewrite get_fun_vis. simpl.
      f_equiv.
      intros ?; simpl.
      apply later_map_ext.
      intros ?; simpl.
      rewrite get_val_ITV.
      simpl.
      reflexivity.
    - rewrite get_val_ITV. simpl. rewrite get_fun_err. reflexivity.
  Qed.

  Program Definition NatOpRSCtx_HOM {S : Set} (op : nat_op)
    (α : @interp_scope F R _ S -n> IT) (env : @interp_scope F R _ S)
    : HOM := exist _ (interp_natoprk rs op α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition NatOpLSCtx_HOM {S : Set} (op : nat_op)
    (α : IT) (env : @interp_scope F R _ S)
    (Hv : AsVal α)
    : HOM := exist _ (interp_natoplk rs op (constO α) (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition AppLSCtx_HOM {S : Set}
    (α : @interp_scope F R _ S -n> IT)
    (env : @interp_scope F R _ S)
    : HOM := exist _ (interp_applk rs α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Transparent LET.
  Program Definition AppRSCtx_HOM {S : Set}
    (β : IT) (env : @interp_scope F R _ S)
    (Hv : AsVal β)
    : HOM := exist _ (interp_apprk rs (constO β) (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - solve_proper_please.
    - rewrite get_val_ITV.
      simpl.
      rewrite get_val_ITV.
      simpl.
      rewrite get_val_tick.
      reflexivity.
    - rewrite get_val_ITV.
      simpl.
      rewrite get_val_vis.
      do 3 f_equiv.
      intro; simpl.
      rewrite get_val_ITV.
      simpl.
      reflexivity.
    - rewrite get_val_ITV.
      simpl.
      rewrite get_val_err.
      reflexivity.
  Qed.
  Opaque LET.

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

  (* | typed_App e₁ e₂ γ α β δ σ τ : *)
  (* (Γ; γ ⊢ₑ e₁ : (Tarr σ α τ β); δ) → *)
  (* (Γ; β ⊢ₑ e₂ : σ; γ) → *)
  (* (Γ; α ⊢ₑ (App e₁ e₂) : τ; δ) *)
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

  Program Definition valid_ectx {S : Set}
    (Γ : S -> ty)
    (e : interp_scope S -n> IT -n> IT)
    `{∀ γ, IT_hom (e γ)}
    (τ α : ty) : iProp :=
    (□ ∀ γ, ssubst_valid Γ γ
            -∗ logrel_ectx (interp_ty τ) (interp_ty α) (exist _ (e γ) _))%I.
  Next Obligation.
    intros; apply _.
  Qed.

  Lemma compat_end {S : Set} (Γ : S → ty) τ
    : ⊢ valid_ectx Γ (interp_cont rs END) τ τ.
  Proof.
    iIntros (γ).
    iModIntro.
    iIntros "#H".
    iApply compat_HOM_id.
  Qed.

  Lemma compat_natop_r {S : Set} (Γ : S → ty) α τ
    op t (E : interp_scope S -n> IT -n> IT)
    `{∀ γ, IT_hom (E γ)}
    `{∀ γ, IT_hom (interp_natoprk _ op t E γ)} :
    ⊢ valid_ectx Γ E Tnat τ
      -∗ valid Γ t Tnat τ α
      -∗ valid_ectx Γ (interp_natoprk _ op t E) Tnat α.
  Proof.
    iIntros "#H #G".
    iIntros (γ).
    iModIntro.
    iIntros "#Hγ".
    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (m) "Hm Hst".

    pose (κ' := (NatOpLSCtx_HOM op (IT_of_V v) γ _)).
    simpl.
    assert (E γ (NATOP (do_natop op) (t γ) (IT_of_V v)) = ((E γ ◎ `κ') (t γ)))
      as -> by done.
    iSpecialize ("G" $! γ with "Hγ").
    unshelve iApply ("G" $! (exist _ (E γ ◎ `κ') _) with "[] Hm Hst").
    { apply _. }
    simpl.

    iIntros (w).
    iModIntro.
    iIntros "#Hw".
    iIntros (m') "Hm Hst".
    simpl.

    iDestruct "Hw" as "(%n & #HEQ1)".
    iDestruct "Hv" as "(%n' & #HEQ2)".
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! (RetV (do_natop op n n')) with "[]").
    {
      iExists _.
      iPureIntro.
      reflexivity.
    }
    iSpecialize ("H" $! m' with "Hm Hst").
    rewrite IT_of_V_Ret.

    iAssert ((NATOP (do_natop op) (IT_of_V w) (IT_of_V v))
               ≡ (Ret (do_natop op n n')))%I as "#HEQ".
    {
      iRewrite "HEQ2".
      rewrite IT_of_V_Ret.
      iAssert ((IT_of_V w) ≡ IT_of_V (RetV n))%I as "#HEQ1'".
      {
        iApply f_equivI.
        iApply "HEQ1".
      }
      rewrite IT_of_V_Ret.
      iAssert (NATOP (do_natop op) (IT_of_V w) (Ret n')
                 ≡ NATOP (do_natop op) (Ret n) (Ret n'))%I as "#HEQ2''".
      {
        unshelve iApply (f_equivI (λne x, NATOP (do_natop op) x (Ret n'))).
        { solve_proper. }
        { solve_proper. }
        iApply "HEQ1'".
      }
      iRewrite "HEQ2''".
      rewrite NATOP_Ret.
      done.
    }
    iRewrite "HEQ".
    simpl.
    iApply "H".
  Qed.

  Lemma compat_natop_l {S : Set} (Γ : S → ty) α τ
    op (t : interp_scope S -n> IT) (E : interp_scope S -n> IT -n> IT)
    `{∀ γ, IT_hom (E γ)}
    `{∀ γ, AsVal (t γ)}
    `{∀ γ, IT_hom (interp_natoplk _ op t E γ)} :
    ⊢ valid_ectx Γ E Tnat τ
      -∗ valid Γ t Tnat τ α
      -∗ valid_ectx Γ (interp_natoplk _ op t E) Tnat α.
  Proof.
    iIntros "#H #G".
    iIntros (γ).
    iModIntro.
    iIntros "#Hγ".
    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (m) "Hm Hst".
    simpl.
    pose (κ' := (NATOP (do_natop op) (IT_of_V v))).
    simpl.
    assert (E γ (NATOP (do_natop op) (IT_of_V v) (t γ)) = ((E γ ◎ κ') (t γ)))
      as -> by done.
    iSpecialize ("G" $! γ with "Hγ").
    unshelve iApply ("G" $! (exist _ (E γ ◎ κ') _) with "[] Hm Hst").
    { apply _. }
    subst κ'.
    simpl.

    iIntros (w).
    iModIntro.
    iIntros "#Hw".
    iIntros (m') "Hm Hst".
    simpl.

    iSpecialize ("H" $! γ with "Hγ").

    iDestruct "Hw" as "(%n & #HEQ1)".
    iDestruct "Hv" as "(%n' & #HEQ2)".
    iSpecialize ("H" $! (RetV (do_natop op n' n)) with "[]").
    {
      iExists _.
      iPureIntro.
      reflexivity.
    }
    iSpecialize ("H" $! m' with "Hm Hst").
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
    iApply "H".
  Qed.

  Lemma compat_ifk {S : Set} (Γ : S -> ty)
    (E : interp_scope S -n> IT -n> IT)
    e₁ e₂
    `{∀ γ, IT_hom (E γ)}
    `{∀ γ, IT_hom (interp_ifk rs e₁ e₂ E γ)}
    (τ α β : ty) :
    ⊢ valid_ectx Γ E τ α
      -∗ valid Γ e₁ τ α β
      -∗ valid Γ e₂ τ α β
      -∗ valid_ectx Γ (interp_ifk rs e₁ e₂ E) Tnat β.
  Proof.
    iIntros "#H #G #J".
    iModIntro.
    iIntros (γ) "#Henv".
    iSpecialize ("H" $! γ with "Henv").

    iIntros (v).
    iModIntro.
    iIntros "#Hv".
    iIntros (σ'') "Hm Hst".
    iDestruct "Hv" as "(%n & #Hv)".
    iRewrite "Hv".
    rewrite IT_of_V_Ret.
    simpl.
    destruct (decide (0 < n)) as [?|?].
    - rewrite IF_True//.
      iSpecialize ("G" $! γ with "Henv").
      unshelve iSpecialize ("G" $! (exist _ (E γ) _)).
      { apply _. }
      iApply ("G" with "H Hm Hst").
    - rewrite IF_False//; last lia.
      iSpecialize ("J" $! γ with "Henv").
      unshelve iSpecialize ("J" $! (exist _ (E γ) _)).
      { apply _. }
      iApply ("J" with "H Hm Hst").
  Qed.

  (* Lemma compat_appk_r {S : Set} (Γ : S → ty) τ α c d e t *)
  (*   (E : interp_scope S -n> IT -n> IT) *)
  (*   `{∀ γ, IT_hom (E γ)} *)
  (*   `{∀ γ, IT_hom (interp_app_contrk _ t E γ)} : *)
  (*   ⊢ valid_ectx Γ E τ α *)
  (*     -∗ valid Γ t c d e *)
  (*     -∗ valid_ectx Γ (interp_app_contrk _ t E) τ α. *)
  (* Proof. *)
  (*   Opaque interp_app_cont. *)
  (*   iIntros "#H #G". *)
  (*   iIntros (γ). *)
  (*   iModIntro. *)
  (*   iIntros "#Hγ". *)
  (*   iIntros (v). *)
  (*   iModIntro. *)
  (*   iIntros "#Hv". *)
  (*   iIntros (m) "Hm Hst". *)
  (*   simpl. *)

  (*   pose (κ'' := (AppContLSCtx_HOM (IT_of_V v) γ _)). *)
  (*   set (F := (E γ) _). *)
  (*   assert (F ≡ (((E γ) ◎ (`κ'')) (t γ))) as ->. *)
  (*   { *)
  (*     subst F. simpl. Transparent interp_app_cont. simpl. *)
  (*     f_equiv. *)
  (*     rewrite ->2 get_val_ITV. *)
  (*     simpl. *)
  (*     reflexivity. *)
  (*   } *)
  (*   pose (sss := (HOM_compose (exist _ (E γ) (H _)) κ'')). *)
  (*   assert (((E γ) ◎ `κ'') = (`sss)) as ->. *)
  (*   { reflexivity. } *)

  (*   iSpecialize ("G" $! γ with "Hγ"). *)
  (*   iSpecialize ("G" $! sss). *)
  (*   iApply ("G" with "[] [] Hst"); *)
  (*     last admit. *)
  (*   iIntros (w). *)
  (*   iModIntro. *)
  (*   iIntros "#Hw". *)
  (*   iIntros (m') "Hm Hst".     *)
  (* Admitted. *)

  (* Lemma compat_appk_l {S : Set} (Γ : S → ty) τ α c d e *)
  (*   (t : interp_scope S -n> IT) *)
  (*   (E : interp_scope S -n> IT -n> IT) *)
  (*   `{∀ γ, IT_hom (E γ)} *)
  (*   `{∀ γ, AsVal (t γ)} *)
  (*   `{∀ γ, IT_hom (interp_app_contlk _ t E γ)} : *)
  (*   ⊢ valid_ectx Γ E τ α *)
  (*     -∗ valid Γ t c d e *)
  (*     -∗ valid_ectx Γ (interp_app_contlk _ t E) τ α. *)
  (* Proof. *)
  (*   Opaque interp_app_cont. *)
  (*   iIntros "#H #G". *)
  (*   iIntros (γ). *)
  (*   assert (AsVal (t γ)). *)
  (*   { apply _. } *)
  (*   iModIntro. *)
  (*   iIntros "#Hγ". *)
  (*   iIntros (v). *)
  (*   iModIntro. *)
  (*   iIntros "#Hv". *)
  (*   iIntros (m) "Hm Hst". *)
  (*   simpl. *)

  (* Admitted. *)

  Lemma compat_cont {S : Set} (Γ : S -> ty) τ σ
    (k : interp_scope S -n> IT -n> IT)
    `{∀ γ : interp_scope S, IT_hom (k γ)}
    : ⊢ valid_ectx Γ k τ σ
        -∗ ∀ α, valid Γ (interp_cont_val rs k) (Tcont τ σ) α α.
  Proof.
    iIntros "#H".
    iIntros (α γ).
    iModIntro.
    iIntros "#Hγ".
    iIntros (κ) "Hκ".
    iIntros (m) "Hm Hst".
    iSpecialize ("H" $! γ with "Hγ").
    unfold interp_cont_val.
    simpl.
    match goal with
    | |- context G [ofe_mor_car _ _ Fun ?a] =>
        set (F := a)
    end.
    iSpecialize ("Hκ" $! (FunV F)).
    iApply ("Hκ" with "[] Hm Hst").
    iExists (exist _ (k γ) (H _)).
    iSplit.
    - subst F.
      Transparent IT_of_V.
      simpl.
      iPureIntro.
      do 2 f_equiv.
      intros ?; simpl.
      rewrite later_map_Next.
      rewrite Tick_eq.
      reflexivity.
    - iModIntro.
      iApply "H".
  Qed.

  Open Scope types.

  Lemma fundamental_expr {S : Set} (Γ : S -> ty) τ α β e :
    Γ; α ⊢ₑ e : τ; β → ⊢ valid Γ (interp_expr rs e) τ α β
  with fundamental_val {S : Set} (Γ : S -> ty) τ α β v :
    Γ; α ⊢ᵥ v : τ; β → ⊢ valid Γ (interp_val rs v) τ α β
  with fundamental_cont {S : Set} (Γ : S -> ty) τ σ κ :
    Γ ⊢ᵪ κ : τ ⤞ σ → ⊢ valid_ectx Γ (interp_cont rs κ) τ σ.
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
      + iPoseProof (fundamental_cont _ _ _ _ _ H) as "H".
        iDestruct (compat_cont with "H") as "G".
        iSpecialize ("G" $! α).
        iApply "G".
    - intros H.
      destruct H.
      + iApply compat_end.
      + iApply compat_ifk;
          [ by iApply fundamental_cont
          | by iApply fundamental_expr
          | by iApply fundamental_expr].
      + iApply compat_natop_l;
          [ by iApply fundamental_cont
          | by iApply fundamental_val].
      + iApply compat_natop_r;
          [ by iApply fundamental_cont
          | by iApply fundamental_expr].
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
