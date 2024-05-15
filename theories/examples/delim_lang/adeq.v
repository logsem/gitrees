From gitrees Require Import gitree lang_generic hom.
From gitrees.effects Require Import delim.
From gitrees.examples.delim_lang Require Import lang interp.
From iris.algebra Require Import list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.

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

Reserved Notation "Γ ';' α '⊢ᵪ' e ':' τ ';' β"
  (at level 90, e at next level, τ at level 20, no associativity).

(* TODO: pure stuff has ∀ σ deeper inside *)
Inductive typed_expr {S : Set} (Γ : S -> ty) :
  ty -> expr S -> ty -> ty -> Prop :=
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
  (Γ; δ ⊢ₑ e₁ : (Tcont τ α); β) →
  (Γ; σ ⊢ₑ e₂ : τ; δ) →
  (Γ; σ ⊢ₑ (AppCont e₁ e₂) : α; β)
| typed_NatOp o e₁ e₂ α β :
  (Γ; α ⊢ₑ e₁ : Tnat; β) →
  (Γ; α ⊢ₑ e₂ : Tnat; β) →
  (Γ; α ⊢ₑ NatOp o e₁ e₂ : Tnat; β)
| typed_If e e₁ e₂ α β σ τ :
  (Γ; σ ⊢ₑ e : Tnat; β) →
  (Γ; α ⊢ₑ e₁ : τ; σ) →
  (Γ; α ⊢ₑ e₂ : τ; σ) →
  (Γ; α ⊢ₑ (if e then e₁ else e₂) : τ; β)
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
| typed_ContV (k : cont S) τ α β :
  (Γ; α ⊢ᵪ k : τ; β) →
  (Γ; α ⊢ᵥ (ContV k) : τ; β)
where "Γ ';' α '⊢ᵥ' e ':' τ ';' β" := (typed_val Γ α e τ β) : types
with typed_cont {S : Set} (Γ : S -> ty) : ty -> cont S -> ty -> ty -> Prop :=
| typed_END τ δ :
  (Γ; δ ⊢ᵪ END : (Tcont τ τ); δ)
| typed_IfK e₁ e₂ α β δ A k τ :
  (Γ; α ⊢ₑ e₁ : τ; β) ->
  (Γ; α ⊢ₑ e₂ : τ; β) ->
  (Γ; β ⊢ᵪ k : Tcont τ A; δ) ->
  (Γ; α ⊢ᵪ IfK e₁ e₂ k : Tcont Tnat A; δ)
(* | typed_AppLK v k α β σ δ τ' τ : *)
(*   (Γ; α ⊢ᵥ v : τ'; β) -> *)
(*   (Γ; β ⊢ᵪ k : Tcont σ τ; δ) -> *)
(*   (Γ; α ⊢ᵪ AppLK v k : Tcont (Tarr τ' α σ δ) τ; δ) *)
(* | typed_AppRK e k τ : *)
(*   (Γ; τ ⊢ᵪ AppRK e k : τ; τ) *)
(* | typed_AppContLK v k τ : *)
(*   (Γ; τ ⊢ᵪ AppContLK v k : τ; τ) *)
(* | typed_AppContRK e k τ : *)
(*   (Γ; τ ⊢ᵪ AppContRK e k : τ; τ) *)
| typed_NatOpLK op v k α β δ τ :
  (Γ; α ⊢ᵥ v : Tnat; β) ->
  (Γ; β ⊢ᵪ k : Tcont Tnat τ; δ) ->
  (Γ; α ⊢ᵪ NatOpLK op v k : Tcont Tnat τ; δ)
| typed_NatOpRK op e k α β δ τ :
  (Γ; α ⊢ₑ e : Tnat; β) ->
  (Γ; β ⊢ᵪ k : Tcont Tnat τ; δ) ->
  (Γ; α ⊢ᵪ NatOpRK op e k : Tcont Tnat τ; δ)
where "Γ ';' α '⊢ᵪ' e ':' τ ';' β" := (typed_cont Γ α e τ β) : types
.

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
  Notation restO := (gState_rest
                       (@sR_idx _ _
                          (sReifier_NotCtxDep_CtxDep reify_delim)) rs ♯ IT).

  Canonical Structure exprO S := leibnizO (expr S).
  Canonical Structure valO S := leibnizO (val S).
  Canonical Structure contO S := leibnizO (cont S).

  Notation "'WP' α {{ β , Φ } }" := (wp rs α notStuck ⊤ (λ β, Φ))
                                      (at level 20, α, Φ at level 200,
                                        format "'WP'  α  {{  β ,  Φ  } }")
      : bi_scope.

  Notation "'WP' α {{ Φ } }" := (wp rs α notStuck ⊤ Φ)
                                  (at level 20, α, Φ at level 200,
                                    format "'WP'  α  {{  Φ  } }") : bi_scope.

  Program Definition has_cont_stack : stateF ♯ IT -> iProp := λ σ,
      (has_substate (σ : sReifier_state reify_delim ♯ IT)
       ∗ ([∗ list] (x : laterO IT -n> laterO IT) ∈ σ,
           ∃ (κ : HOM), x ≡ (laterO_map κ)))%I.

  Lemma wp_shift (σ : stateF ♯ IT) (f : (laterO IT -n> laterO IT) -n> laterO IT)
    (k : IT -n> IT) β {Hk : IT_hom k} Φ :
    laterO_map 𝒫 (f (laterO_map k)) ≡ Next β →
    has_cont_stack σ -∗
    ▷ (£ 1 -∗ has_cont_stack σ -∗ WP β {{ Φ }}) -∗
    WP (k (SHIFT f)) {{ Φ }}.
  Proof.
    iIntros (Hp) "(Hs & G) Ha".
    iApply (wp_shift with "[Hs]"); [done | done |].
    iNext.
    iIntros "HCr Hs".
    iApply ("Ha" with "HCr").
    iFrame.
  Qed.

  Lemma wp_reset (σ : stateF ♯ IT) (e : IT) (k : IT -n> IT) {Hk : IT_hom k}
    Φ :
    has_cont_stack σ -∗
    ▷ (£ 1 -∗ has_cont_stack ((laterO_map k) :: σ) -∗
       WP 𝒫 e {{ Φ }}) -∗
    WP k $ (RESET (Next e)) {{ Φ }}.
  Proof.
    iIntros "(Hs & G) Ha".
    iApply (wp_reset with "[Hs]"); [done |].
    iNext.
    iIntros "HCr Hs".
    iApply ("Ha" with "HCr").
    iFrame.
    unshelve eset (F := exist _ k _ : HOM); first done.
    iExists F.
    now subst F.
  Qed.

  Lemma wp_pop_end (v : IT)
    {HV : AsVal v}
    Φ :
    has_cont_stack [] -∗
    ▷ (£ 1 -∗ has_cont_stack [] -∗ WP v {{ Φ }}) -∗
    WP 𝒫 v {{ Φ }}.
  Proof.
    iIntros "(Hs & G) Ha".
    iApply (wp_pop_end with "Hs").
    iNext.
    iIntros "HCr Hs".
    iApply ("Ha" with "HCr").
    now iFrame.
  Qed.

  Lemma wp_pop_cons (σ : stateF ♯ IT) (v : IT) (k : IT -n> IT)
    {HV : AsVal v}
    Φ :
    has_cont_stack ((laterO_map k) :: σ) -∗
    ▷ (£ 1 -∗ has_cont_stack σ -∗ WP k $ v {{ Φ }}) -∗
    WP 𝒫 v {{ Φ }}.
  Proof.
    iIntros "(Hs & (_ & G)) Ha".
    iApply (wp_pop_cons with "Hs").
    iNext.
    iIntros "HCr Hs".
    iApply ("Ha" with "HCr").
    iFrame.
  Qed.

  Lemma wp_app_cont (σ : stateF ♯ IT) (e : laterO IT) (k' : laterO (IT -n> IT))
    (k : IT -n> IT) β {Hk : IT_hom k}
    Φ :
    laterO_ap k' e ≡ Next β →
    has_cont_stack σ -∗
    ▷ (£ 1 -∗ has_cont_stack ((laterO_map k) :: σ) -∗
       WP β {{ Φ }}) -∗
    WP k (APP_CONT e k') {{ Φ }}.
  Proof.
    iIntros (Hb) "(Hs & G) Ha".
    iApply (wp_app_cont with "Hs");
      first done.
    iNext.
    iIntros "HCr Hs".
    iApply ("Ha" with "HCr").
    iFrame.
    unshelve eset (F := exist _ k _ : HOM); first done.
    iExists F.
    now subst F.
  Qed.

  Program Definition logrel_nat : ITV -n> iProp :=
    λne βv, (∃ (n : natO), βv ≡ RetV n)%I.
  Next Obligation. solve_proper. Qed.

  Definition logrel_ectx (V W : ITV -n> iProp) (κ : HOM) : iProp :=
    (□ ∀ (βv : ITV) σ,
       has_cont_stack σ
       -∗ V βv -∗ WP (`κ (IT_of_V βv)) {{ βv, W βv ∗ has_cont_stack σ }})%I.
  Local Instance logrel_ectx_ne :
    ∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) logrel_ectx.
  Proof. solve_proper. Qed.

  Program Definition logrel_expr
    (τ α β : ITV -n> iProp) : IT -n> iProp :=
    λne βe,
      (∀ (κ : HOM) (σ : stateF ♯ IT),
         logrel_ectx τ α κ
         -∗ has_cont_stack σ
         -∗ WP (`κ βe) {{ βv, β βv ∗ has_cont_stack σ }})%I.
  Next Obligation. solve_proper. Qed.
  Local Instance logrel_expr_ne
    : (∀ n, Proper (dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n)
              logrel_expr).
  Proof. solve_proper. Qed.

  Program Definition logrel_arr (τ α σ β : ITV -n> iProp) : ITV -n> iProp :=
    λne βf,
      (∃ f,
         IT_of_V βf ≡ Fun f
         ∧ □ ∀ (βv : ITV),
         τ βv
         -∗ logrel_expr σ α β (APP' (Fun f) (IT_of_V βv)))%I.
  Next Obligation. solve_proper. Qed.

  Program Definition logrel_cont V W : ITV -n> iProp :=
    λne (βv : ITV), (∃ (κ : HOM),
                       (IT_of_V βv) ≡ (Fun (Next (λne x, Tau (laterO_map (`κ) (Next x)))))
                       ∧ □ logrel_ectx V W κ)%I.
  Next Obligation. intros. apply denot_cont_ne. Defined.
  Next Obligation. solve_proper. Qed.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tnat => logrel_nat
    | Tcont α β => logrel_cont (interp_ty α) (interp_ty β)
    | Tarr τ α σ β => logrel_arr (interp_ty τ) (interp_ty α)
                       (interp_ty σ) (interp_ty β)
    end.

  Program Definition logrel (τ α β : ty) : IT -n> iProp
    := λne e, logrel_expr (interp_ty τ) (interp_ty α) (interp_ty β) e.
  Next Obligation. solve_proper. Qed.

  Local Instance interp_ty_persistent (τ : ty) α :
    Persistent (interp_ty τ α).
  Proof.
    revert α. induction τ=> α; simpl.
    - apply _.
    - apply _.
    - apply _.
  Qed.

  Program Definition ssubst_valid {S : Set}
    (Γ : S -> ty)
    (ss : interp_scope S) : iProp :=
    (∀ x α, □ logrel (Γ x) α α (ss x))%I.

  Program Definition valid {S : Set}
    (Γ : S -> ty)
    (e : interp_scope S -n> IT)
    (τ α β : ty) : iProp :=
    (□ ∀ γ, ssubst_valid Γ γ -∗ logrel τ α β (e γ))%I.

  Program Definition 𝒫_HOM : @HOM sz CtxDep R _ _ := exist _ 𝒫 _.
  Next Obligation. apply _. Qed.

  Lemma 𝒫_logrel_cont τ : ⊢ logrel_ectx (interp_ty τ) (interp_ty τ) 𝒫_HOM.
  Proof.
    iLöb as "IH".
    iModIntro.
    iIntros (αv σ) "G #H".
    destruct σ as [| ? σ].
    - iApply (wp_pop_end with "G").
      iNext.
      iIntros "_ G".
      iApply wp_val.
      iModIntro.
      by iFrame "H".
      (* by iExists []. *)
    - admit.
  Admitted.

  Lemma compat_reset {S : Set} (Γ : S -> ty) e τ' τ A :
        ⊢ valid Γ e τ' τ' τ -∗ valid Γ (interp_reset rs e) τ A A.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Henv".
    iIntros (κ σ) "#Hκ Hσ".
    iApply (wp_reset with "Hσ").
    iNext.
    iIntros "_ Hσ".
    iSpecialize ("H" $! γ with "Henv").
    iSpecialize ("H" $! HOM_id (laterO_map (`κ) :: σ) with "[] Hσ").
    - iModIntro.
      iIntros (βv σ') "Hσ' #H".
      iApply wp_val.
      iModIntro.
      by iFrame "H".
      (* by iExists σ'. *)
    - simpl.
      admit.
  Admitted.

  Lemma compat_shift {S : Set} (Γ : S -> ty) e τ' α τ β :
    ⊢ valid (Γ ▹ (Tcont τ α)) e τ' τ' β
      -∗ valid Γ (interp_shift _ e) τ α β.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Henv".
    iIntros (κ σ) "#Hκ Hσ".
    assert (interp_shift rs e γ ≡ idfun $ interp_shift rs e γ) as ->.
    { reflexivity. }
    iApply (wp_shift with "Hσ").
    { apply (laterO_map_Next 𝒫). }
    {
      iNext.
      iIntros "HCr Hσ'".
      set (F := Next _).
      set (γ' := extend_scope γ _).
      iSpecialize ("H" $! γ' with "[Hκ]").
      - iIntros (x); destruct x as [| x].
        + iIntros (a).
          iModIntro.
          iIntros (Pα σ') "#Hκ' Hσ".
          iApply ("Hκ'" $! (FunV F) σ' with "Hσ").
          iExists κ.
          iSplit; first (iPureIntro; reflexivity).
          iModIntro.
          iModIntro.
          iIntros (βv σ'') "Hσ'' #HHH".
          iApply ("Hκ" with "Hσ'' HHH").
        + iIntros (a).
          iModIntro.
          iApply "Henv".
      - iSpecialize ("H" $! 𝒫_HOM σ).
        iSpecialize ("H" with "[] Hσ'").
        + iApply 𝒫_logrel_cont.
        + iApply "H".
    }
  Qed.

  Lemma compat_var {S : Set} (Γ : S -> ty) (x : S) α :
    ⊢ valid Γ (interp_var x) (Γ x) α α.
  Proof.
    iModIntro.
    iIntros (γ) "#Hss".
    iApply "Hss".
  Qed.

  Lemma compat_nat {S : Set} (Γ : S → ty) n α :
    ⊢ valid Γ (interp_nat rs n) Tnat α α.
  Proof.
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ σ) "#Hκ Hσ".
    iApply (wp_wand with "[Hκ Hσ]").
    - iApply ("Hκ" $! (RetV n) σ with "Hσ").
      iExists _; by iPureIntro.
    - iIntros (v) "(#H & G)".
      iModIntro.
      iFrame "H".
      iFrame "G".
  Qed.

  Lemma logrel_of_val τ v α :
    interp_ty τ v -∗ logrel τ α α (IT_of_V v).
  Proof.
    iIntros "#H".
    iIntros (κ σ) "#Hκ Hσ".
    iApply (wp_wand with "[Hκ Hσ]").
    - by iApply ("Hκ" $! v σ with "Hσ").
    - iIntros (w) "(#G & F)".
      iModIntro.
      iFrame "G".
      iFrame "F".
  Qed.

  Lemma compat_recV {S : Set} (Γ : S -> ty)
    τ1 α τ2 β E e :
    ⊢ valid ((Γ ▹ (Tarr τ1 α τ2 β) ▹ τ1)) e τ2 α β
      -∗ valid Γ (interp_rec rs e) (Tarr τ1 α τ2 β) E E.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Henv".
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
    iIntros (v) "#Hv".
    (* iIntros (κ σ) "Hκ Hσ". *)
    (* rewrite APP_APP'_ITV APP_Fun laterO_map_Next -Tick_eq. *)
    (* pose (γ' := (extend_scope (extend_scope γ (interp_rec rs e γ)) (IT_of_V v))). *)
    (* rewrite /logrel. *)
    (* iSpecialize ("H" $! γ' with "[Hw]"). *)
    (* { *)
    (*   iIntros (x). *)
    (*   destruct x as [| [| x]]; iIntros (ξ); iModIntro. *)
    (*   * iApply logrel_of_val. *)
    (*     iApply "Hw". *)
    (*   * simpl.         *)
    (*     iIntros (σ' κ') "Hκ' Hσ'". *)
    (*     iRewrite "Hf". *)
    (*     iApply (wp_pop_cons with "Hσ'"). *)
    (*     iDestruct "Hκ'" as "(%g & #HEQ & Hκ')". *)
    (*     Transparent IT_of_V. *)
    (*     iDestruct (Fun_inj' with "HEQ") as "HEQ'". *)
    (*     iNext. *)
    (*     iIntros "HCr Hσ'". *)
    (*     iSpecialize ("Hκ'" $! (FunV (Next f))). *)
    (*     iSpecialize ("Hκ'" with "[]"). *)
    (*     { *)
    (*       iExists (Next f). *)
    (*       iSplit; first done. *)
    (*       iModIntro. *)
    (*       iIntros (v') "Hv'". *)
    (*       by iApply "IH". *)
    (*     } *)
    (*     iSpecialize ("Hκ'" $! σ' with "Hσ'"). *)
    (*     iAssert ((`κ') (IT_of_V (FunV (Next f))) *)
    (*                ≡ (`g) (IT_of_V (FunV (Next f))))%I as "HEQ''". *)
    (*     { *)
    (*       unshelve iPoseProof *)
    (*         (f_equivI (λne (f' : IT -n> IT), *)
    (*              f' (Fun (Next f))) (`κ') (`g) with "[HEQ']") as "GGG"; *)
    (*         first solve_proper; first solve_proper; first done. *)
    (*       iApply "GGG". *)
    (*     } *)
    (*     simpl. *)
    (*     iRewrite "HEQ''". *)
    (*     iExact "Hκ'". *)
    (*   * iApply "Henv". *)
    (* } *)
    (* Opaque extend_scope. *)
    (* simpl. *)
    (* rewrite hom_tick. *)
    (* iApply wp_tick. *)
    (* iNext. *)
    (* subst γ'. *)
    (* iApply ("H" with "Hκ Hσ"). *)
  Admitted.

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

  Lemma compat_appcont {S : Set} (Γ : S -> ty) e1 e2 τ α δ β σ :
    valid Γ e1 (Tcont τ σ) σ δ
    -∗ valid Γ e2 τ δ β
    -∗ valid Γ (interp_app_cont _ e1 e2) α σ β.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Henv".
    iIntros (κ σ') "#Hκ Hσ'".

    pose (κ' := (AppContRSCtx_HOM e1 γ)).
    assert ((interp_app_cont rs e1 e2 γ) = ((`κ') (e2 γ))) as ->.
    { simpl. reflexivity. }
    assert ((`κ) ((`κ') (e2 γ)) = ((`κ) ◎ (`κ')) (e2 γ)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }

    iSpecialize ("G" $! γ with "Henv").
    iApply ("G" $! sss σ' with "[] Hσ'").

    iIntros (w σ'').
    iModIntro.
    iIntros "Hσ #Hw".
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
    iApply ("H" $! sss σ'' with "[] Hσ").

    iIntros (v σ''').
    iModIntro.
    iIntros "Hσ #Hv".
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
    iApply (wp_app_cont with "[Hσ]").
    { reflexivity. }
    - iFrame "Hσ".
    - iNext.
      iIntros "_ Hσ".
      simpl.
      rewrite later_map_Next.
      rewrite <- Tick_eq.
      iApply wp_tick.
      iNext.
      (* iApply ("Hv" $! w (laterO_map (`κ) :: σ''') with "Hσ Hw"). *)
      admit.
  Admitted.

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

  Lemma compat_nat_op {S : Set} (Γ : S → ty)
    D E F e1 e2 op :
    ⊢ valid Γ e1 Tnat E F
      -∗ valid Γ e2 Tnat F D
      -∗ valid Γ (interp_natop rs op e1 e2) Tnat E D.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ σ) "#Hκ Hσ".
    rewrite /interp_natop //=.

    set (κ' := (NatOpRSCtx_HOM op e1 γ)).
    assert ((NATOP (do_natop op) (e1 γ) (e2 γ)) = ((`κ') (e2 γ))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.

    iSpecialize ("G" $! γ with "Hγ").
    iApply ("G" $! sss σ with "[] Hσ").

    iIntros (w σ').
    iModIntro.
    iIntros "Hσ #Hw".
    subst sss.
    subst κ'.
    simpl.

    pose (κ' := (NatOpLSCtx_HOM op (IT_of_V w) γ _)).
    assert ((NATOP (do_natop op) (e1 γ) (IT_of_V w)) = ((`κ') (e1 γ))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ κ')). rewrite (HOM_compose_ccompose κ κ' sss)//.

    iSpecialize ("H" $! γ with "Hγ").
    iApply ("H" $! sss σ' with "[] Hσ").

    iIntros (v σ'').
    iModIntro.
    iIntros "Hσ #Hv".
    subst sss.
    subst κ'.
    simpl.

    iDestruct "Hw" as "(%n & #HEQ1)".
    iDestruct "Hv" as "(%n' & #HEQ2)".

    (* iApply ("Hκ" $! (RetV (do_natop op n n')) σ'' with "Hσ"). *)
    (* iExists _. *)
    (* iPureIntro. *)
    (* reflexivity. *)
  Admitted.

  Program Definition AppRSCtx_HOM {S : Set}
    (α : @interp_scope F R _ S -n> IT)
    (env : @interp_scope F R _ S)
    : HOM := exist _ (interp_apprk rs α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition AppLSCtx_HOM {S : Set}
    (β : IT) (env : @interp_scope F R _ S)
    (Hv : AsVal β)
    : HOM := exist _ (interp_applk rs (constO β) (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  (* evaluation order things *)
  Lemma compat_app {S : Set} (Γ : S → ty)
    A B C D E F e1 e2 :
    ⊢ valid Γ e1 (Tarr A C B E) E F
      -∗ valid Γ e2 A F D
      -∗ valid Γ (interp_app rs e1 e2) B C D.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ σ) "#Hκ Hσ".
    rewrite /interp_app //=.

    pose (κ' := (AppRSCtx_HOM e1 γ)).
    assert ((e1 γ ⊙ (e2 γ)) = ((`κ') (e2 γ))) as ->.
    { simpl; unfold AppRSCtx. reflexivity. }
    assert ((`κ) ((`κ') (e2 γ)) = ((`κ) ◎ (`κ')) (e2 γ)) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ')).
    assert ((`κ ◎ `κ') = (`sss)) as ->.
    { reflexivity. }

    iSpecialize ("G" $! γ with "Hγ").
    iApply ("G" $! sss σ with "[] Hσ").

    iIntros (w σ').
    iModIntro.
    iIntros "Hσ #Hw".
    subst sss.
    subst κ'.
    simpl.

    pose (κ'' := (AppLSCtx_HOM (IT_of_V w) γ _)).
    assert (((`κ) (e1 γ ⊙ (IT_of_V w))) = (((`κ) ◎ (`κ'')) (e1 γ))) as ->.
    { reflexivity. }
    pose (sss := (HOM_compose κ κ'')).
    assert ((`κ ◎ `κ'') = (`sss)) as ->.
    { reflexivity. }

    iSpecialize ("H" $! γ with "Hγ").
    iApply ("H" $! sss σ' with "[] Hσ").

    iIntros (v σ'').
    iModIntro.
    iIntros "Hσ #Hv".
    subst sss.
    subst κ''.
    simpl.

    iDestruct "Hv" as "(%n' & #HEQ & Hv)".
    (* iRewrite "HEQ". *)
  Admitted.

End logrel.

Local Definition rs : gReifiers CtxDep 1 :=
  gReifiers_cons reify_delim gReifiers_nil.

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logpred_adequacy cr Σ R `{!Cofe R, SubOfe natO R}
  `{!invGpreS Σ} `{!statePreG rs R Σ} τ β'
  (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R)
  (β : IT (gReifiers_ops rs) R) st st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ},
      (£ cr ⊢ valid rs □ α τ τ β')%I) →
  ssteps (gReifiers_sReifier rs) (α ı_scope) st β st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V β) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1)
      ∨ (∃ e, β ≡ Err e ∧ notStuck e)).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety cr); eauto.
  { apply Hdisj. }
  { by rewrite Hb. }
  intros H1 H2.
  exists (λ _, True)%I. split. (* (interp_ty _ τ)%I *)
  { apply _. }
  iIntros "[Hcr  Hst]".
  iPoseProof (Hlog with "Hcr") as "Hlog".
  destruct st as [σ []].
  iAssert (has_substate σ) with "[Hst]" as "Hs".
  { unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) _) (σ,()) ≡
              of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state σ)) as ->;
                                                                            last done.
    intro j. unfold sR_idx. simpl.
    unfold of_state, of_idx.
    destruct decide as [Heq|]; last first.
    { inv_fin j; first done.
      intros i. inversion i. }
    inv_fin j; last done.
    intros Heq.
    rewrite (eq_pi _ _ Heq eq_refl)//.
  }
  iSpecialize ("Hlog" $! ı_scope with "[]").
  { iIntros ([]). }
  iSpecialize ("Hlog" $! HOM_id with "[]").
  {
    iModIntro.
    iIntros (αv σ'') "HHH GGG".
    simpl.
    iApply wp_val.
    iModIntro.
    iFrame.
  }
  iSpecialize ("Hlog" with "[Hs]").
  {
    admit.
  }
  iApply (wp_wand with "Hlog").
  iIntros (βv). simpl.
  iIntros "_".
  done.
Admitted.
