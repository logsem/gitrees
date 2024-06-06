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
where "Γ ';' α '⊢ᵥ' e ':' τ ';' β" := (typed_val Γ α e τ β) : types
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

  Definition logrel_nat' {S : Set} (βv : ITV) (v : valO S) : iProp :=
    (∃ (n : natO), βv ≡ RetV n ∧ v ≡ LitV n)%I.
  Local Instance logrel_nat_ne {S : Set} : NonExpansive2 (@logrel_nat' S).
  Proof. solve_proper. Qed.
  Program Definition logrel_nat {S : Set} : ITV -n> valO S -n> iProp :=
    λne x y, @logrel_nat' S x y.
  Solve All Obligations with solve_proper.
  Fail Next Obligation.

  Definition obs_ref' {S : Set}
    (t : IT) (κ : HOM) (σ : stateF ♯ IT)
    (e : exprO S) (k : contO S) (m : mcontO S)
    : iProp :=
    (has_substate σ
     -∗ WP (𝒫 (`κ t)) {{ βv, has_substate []
                             ∗ ∃ (v : valO S) (nm : nat * nat),
                                 ⌜steps (Ceval e k m) (Cret v) nm⌝ }})%I.
  Local Instance obs_ref_ne {S : Set} :
    ∀ n, Proper (dist n ==> dist n ==> dist n ==>
                   dist n ==> dist n ==> dist n ==> dist n)
           (@obs_ref' S).
  Proof. solve_proper. Qed.
  Local Instance obs_ref_proper {S : Set} :
    Proper ((≡) ==> (≡) ==> (≡) ==>
              (≡) ==> (≡) ==> (≡) ==> (≡))
      (@obs_ref' S).
  Proof. solve_proper. Qed.

  Program Definition obs_ref {S : Set}
    : IT -n> HOM -n> (stateF ♯ IT)
                     -n> exprO S -n> contO S -n> mcontO S -n> iProp :=
    λne x y z a b c, obs_ref' x y z a b c.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    intros.
    intros ????????; simpl.
    solve_proper.
  Qed.

  Definition logrel_mcont' {S : Set}
    (P : ITV -n> valO S -n> iProp) (F : stateF ♯ IT) (m : mcontO S) :=
    (∀ αv v, P αv v -∗ obs_ref (IT_of_V αv) HOM_id F (Val v) END m)%I.
  Local Instance logrel_mcont_ne {S : Set} :
    NonExpansive3 (@logrel_mcont' S).
  Proof. solve_proper. Qed.
  Local Instance logrel_mcont_proper {S : Set} :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡))
      (@logrel_mcont' S).
  Proof. solve_proper. Qed.
  Program Definition logrel_mcont {S : Set} :
    (ITV -n> valO S -n> iProp)
    -n> (stateF ♯ IT) -n> mcontO S -n> iProp
    := λne x y z, logrel_mcont' x y z.
  Solve All Obligations with solve_proper.

  Program Definition logrel_ectx' {S : Set}
    (Pτ Pα : ITV -n> valO S -n> iProp) (κ : HOM) (k : cont S)
    : iProp :=
    (□ ∀ αv v, Pτ αv v -∗ ∀ σ (m : mcontO S),
       logrel_mcont Pα σ m -∗ obs_ref (IT_of_V αv) κ σ (Val v) k m)%I.
  Local Instance logrel_ectx_ne {S : Set} :
    NonExpansive4 (@logrel_ectx' S).
  Proof. solve_proper. Qed.
  Local Instance logrel_ectx_proper {S : Set} :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
      (@logrel_ectx' S).
  Proof. solve_proper. Qed.
  Program Definition logrel_ectx {S : Set}
    : (ITV -n> valO S -n> iProp) -n> (ITV -n> valO S -n> iProp)
                                     -n> HOM -n> cont S -n> iProp
    := λne x y z w, logrel_ectx' x y z w.
  Solve All Obligations with solve_proper.

  Program Definition logrel_cont' {S : Set}
    (V W : ITV -n> valO S -n> iProp) (βv : ITV) (v : valO S) : iProp :=
    (∃ (κ : HOM) K, (IT_of_V βv) ≡
                      (Fun (Next (λne x, Tau (laterO_map (𝒫 ◎ `κ) (Next x)))))
                    ∧ ⌜v = ContV K⌝
                    ∧ □ logrel_ectx V W κ K)%I.
  Local Instance logrel_cont_ne {S : Set} : NonExpansive4 (@logrel_cont' S).
  Proof. solve_proper. Qed.
  Local Instance logrel_cont_proper {S : Set} :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
      (@logrel_cont' S).
  Proof. solve_proper. Qed.
  Program Definition logrel_cont {S : Set}
    : (ITV -n> valO S -n> iProp) -n> (ITV -n> valO S -n> iProp)
                                     -n> ITV -n> valO S -n> iProp
    := λne x y z w, logrel_cont' x y z w.
  Solve All Obligations with solve_proper.

  Program Definition logrel_arr' {S : Set}
    (Pτ Pα Pσ Pβ : ITV -n> valO S -n> iProp) (f : ITV) (vf : valO S)
    : iProp
    := (∃ f', IT_of_V f ≡ Fun f'
              ∧ □ ∀ (βv : ITV) (v : valO S),
          Pτ βv v -∗ ∀ (κ : HOM) (K : cont S),
          logrel_ectx Pσ Pα κ K -∗ ∀ σ m,
          logrel_mcont Pβ σ m
          -∗ obs_ref (APP' (Fun f') (IT_of_V βv)) κ σ
               (App (Val vf) (Val v)) K m)%I.
  Local Instance logrel_arr_ne {S : Set}
    : (∀ n, Proper (dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n
                      ==> dist n)
              (@logrel_arr' S)).
  Proof. solve_proper. Qed.
  Local Instance logrel_arr_proper {S : Set} :
    Proper ((≡) ==> (≡) ==> (≡) ==>
              (≡) ==> (≡) ==> (≡) ==> (≡))
      (@logrel_arr' S).
  Proof. solve_proper. Qed.
  Program Definition logrel_arr {S : Set}
    : (ITV -n> valO S -n> iProp)
      -n> (ITV -n> valO S -n> iProp)
          -n> (ITV -n> valO S -n> iProp)
              -n> (ITV -n> valO S -n> iProp) -n> ITV -n> valO S -n> iProp :=
    λne x y z w v t, logrel_arr' x y z w v t.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    intros; intros ????????; simpl.
    solve_proper.
  Qed.
    
  Fixpoint interp_ty {S : Set} (τ : ty) : ITV -n> valO S -n> iProp :=
    match τ with
    | Tnat => logrel_nat
    | Tcont α β => logrel_cont (interp_ty α) (interp_ty β)
    | Tarr τ α σ β => logrel_arr (interp_ty τ) (interp_ty α)
                       (interp_ty σ) (interp_ty β)
    end.

  Local Instance interp_ty_persistent {S : Set} (τ : ty) α v :
    Persistent (@interp_ty S τ α v).
  Proof.
    revert α. induction τ=> α; simpl.
    - unfold logrel_nat. apply _.
    - unfold logrel_arr. apply _.
    - unfold logrel_cont. apply _.
  Qed.

  Program Definition logrel_expr {S : Set}
    (τ α δ : ITV -n> valO S -n> iProp) : IT -n> exprO S -n> iProp
    := λne e e', (∀ E E', logrel_ectx τ α E E'
                    -∗ ∀ F F', logrel_mcont δ F F'
                            -∗ obs_ref e E F e' E' F')%I.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    intros; intros ????; simpl.
    do 2 (f_equiv; intro; simpl).
    f_equiv.
    do 2 (f_equiv; intro; simpl).
    f_equiv.
    solve_proper.
  Qed.  
  
  Definition logrel {S : Set} (τ α β : ty) : IT -n> exprO S -n> iProp
    := logrel_expr (interp_ty τ) (interp_ty α) (interp_ty β).

  Program Definition ssubst_valid {S : Set}
    (Γ : S -> ty)
    (ss : interp_scope S) (γ : S [⇒] Empty_set) : iProp :=
    (∀ x τ, □ logrel (Γ x) τ τ (ss x) (γ x))%I.

  Program Definition valid {S : Set}
    (Γ : S -> ty)
    (e : interp_scope S -n> IT)
    (e' : exprO S)
    (τ α σ : ty) : iProp :=
    (□ ∀ γ (γ' : S [⇒] Empty_set), ssubst_valid Γ γ γ'
          -∗ @logrel Empty_set τ α σ (e γ) (bind (F := expr) γ' e'))%I.

  (* Lemma compat_empty {S : Set} P : *)
  (*   ⊢ @logrel_mcont S P [] []. *)
  (* Proof. *)
  (*   iIntros (v v') "Pv HH". *)
  (*   iApply (wp_pop_end with "HH"). *)
  (*   iNext. *)
  (*   iIntros "_ HHH". *)
  (*   iApply wp_val. *)
  (*   iModIntro. *)
  (*   iFrame "HHH". *)
  (*   iExists v'. *)
  (*   iExists (1, 1). *)
  (*   iPureIntro. *)
  (*   eapply (steps_many _ _ _ 0 0 1 1 1 1); *)
  (*     [done | done | apply Ceval_val |]. *)
  (*   eapply (steps_many _ _ _ 0 0 1 1 1 1); *)
  (*     [done | done | apply Ccont_end |]. *)
  (*   eapply (steps_many _ _ _ 1 1 0 0 1 1); *)
  (*     [done | done | apply Cmcont_ret |]. *)
  (*   constructor. *)
  (* Qed. *)

  (* Lemma compat_cons {S : Set} P Q (x : HOM) (x' : contO S) *)
  (*   (xs : list (later IT -n> later IT)) xs' : *)
  (*   ⊢ logrel_ectx P Q x x' *)
  (*     -∗ logrel_mcont Q xs xs' *)
  (*     -∗ logrel_mcont P (laterO_map (𝒫 ◎ `x) :: xs) (x' :: xs'). *)
  (* Proof. *)
  (*   iIntros "#H G". *)
  (*   iIntros (v v') "Hv Hst". *)
  (*   iApply (wp_pop_cons with "Hst"). *)
  (*   iNext. *)
  (*   iIntros "_ Hst". *)
  (*   iSpecialize ("H" $! v with "Hv"). *)
  (*   iSpecialize ("H" $! xs xs' with "G Hst"). *)
  (*   iApply (wp_wand with "H"). *)
  (*   iIntros (_) "(H1 & (%w & %nm & %H2))". *)
  (*   destruct nm as [n m]. *)
  (*   iModIntro. *)
  (*   iFrame "H1". *)
  (*   iExists w, (n, m). *)
  (*   iPureIntro. *)
  (*   eapply (steps_many _ _ _ 0 0 n m n m); *)
  (*     [done | done | apply Ceval_val |]. *)
  (*   eapply (steps_many _ _ _ 0 0 n m n m); *)
  (*     [done | done | apply Ccont_end |]. *)
  (*   eapply (steps_many _ _ _ 1 1 0 0 1 1); *)
  (*     [done | done | apply Cmcont_ret |]. *)
  (*   constructor. *)
  (* Qed. *)

  Lemma compat_HOM_id {S : Set} P :
    ⊢ @logrel_ectx S P P HOM_id END.
  Proof.
    iIntros (v v').
    iModIntro.
    iIntros "Pv".
    iIntros (σ m) "Hσ HH".
    iApply ("Hσ" with "Pv HH").
  Qed.

  Lemma logrel_of_val {S : Set} τ α v (v' : valO S) :
    interp_ty α v v' -∗ logrel α τ τ (IT_of_V v) (Val v').
  Proof.
    iIntros "#H".
    iIntros (κ K) "Hκ".
    iIntros (σ m) "Hσ Hown".
    iApply ("Hκ" with "H Hσ Hown").
  Qed.

  Lemma compat_var {S : Set} (Γ : S -> ty) (x : S) :
    ⊢ (∀ α, valid Γ (interp_var x) (Var x) (Γ x) α α).
  Proof.
    iIntros (α).
    iModIntro.
    iIntros (γ γ') "#Hss".
    iIntros (E E') "HE".
    iIntros (F F') "HF".
    iIntros "Hσ".
    iApply ("Hss" with "HE HF Hσ").
  Qed.

  Lemma compat_reset {S : Set} (Γ : S -> ty) e (e' : exprO S) σ τ :
    ⊢ valid Γ e e' σ σ τ -∗ (∀ α, valid Γ (interp_reset rs e) (reset e') τ α α).
  Proof.
    iIntros "#H".
    iIntros (α).
    iModIntro.
    iIntros (γ γ') "Hγ".
    iIntros (κ κ') "Hκ".
    iIntros (m m') "Hm Hst".
    assert (𝒫 ((`κ) (interp_reset rs e γ))
              ≡ (𝒫 ◎ `κ) (interp_reset rs e γ)) as ->.
    { reflexivity. }
    iApply (wp_reset with "Hst").
    iNext.
    iIntros "_ Hst".
    iSpecialize ("H" $! γ with "Hγ").
    unshelve iSpecialize ("H" $! HOM_id END (compat_HOM_id _)
                            (laterO_map (𝒫 ◎ `κ) :: m) (κ' :: m'));
      first apply _.
    iAssert (logrel_mcont (interp_ty τ) (laterO_map (𝒫 ◎ `κ) :: m) (κ' :: m'))
      with "[Hm Hκ]" as "Hm".
    {
      iIntros (v v') "Hv Hst".
      iApply (wp_pop_cons with "Hst").
      iNext.
      iIntros "_ Hst".
      iSpecialize ("Hκ" $! v with "Hv").
      iSpecialize ("Hκ" $! m with "Hm").
      iSpecialize ("Hκ" with "Hst").
      iApply (wp_wand with "Hκ").
      iIntros (_) "(H1 & (%w & %nm & %H2))".
      iModIntro.
      iFrame "H1".
      iExists w, nm.
      iPureIntro.
      admit.
    }
    iSpecialize ("H" with "Hm Hst").
    iApply (wp_wand with "H").
    iIntros (_) "(H1 & (%w & %nm & %H2))".
    destruct nm as [a b].
    iModIntro.
    iFrame "H1".
    iExists w, ((a + 1)%nat, (b + 1)%nat).
    iPureIntro.
    term_simpl.
    eapply (steps_many _ _ _ 1 1 a b (a + 1)%nat (b + 1)%nat);
      [ lia | lia | apply Ceval_reset |].
    assumption.
  Admitted.

  Program Definition 𝒫_HOM : @HOM sz CtxDep R _ rs := exist _ 𝒫 _.
  Next Obligation.
    apply _.
  Qed.

  Lemma compat_shift {S : Set} (Γ : S -> ty) e (e' : exprO (inc S)) σ α τ β :
    ⊢ valid (Γ ▹ (Tcont τ α)) e e' σ σ β -∗ valid Γ (interp_shift _ e) (Shift e') τ α β.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ γ') "#Hγ".
    iIntros (κ κ') "#Hκ".
    iIntros (m m') "Hm Hst".
    assert (𝒫 ((`κ) (interp_shift rs e γ))
              ≡ (𝒫 ◎ `κ) (interp_shift rs e γ)) as ->.
    { reflexivity. }
    iApply (wp_shift with "Hst").
    { rewrite laterO_map_Next; reflexivity. }
    iNext.
    iIntros "_ Hst".
    match goal with
    | |- context G [ofe_mor_car _ _ e ?a] =>
        set (γ_ := a)
    end.
    pose (γ_' := ((mk_subst (Val (ContV κ')%syn)) ∘ (γ' ↑)%bind)%bind : inc S [⇒] ∅).
    iAssert (ssubst_valid (Γ ▹ Tcont τ α) γ_ γ_') with "[Hγ Hκ]" as "Hγ'".
    {
      iIntros (x τ').
      destruct x as [| x].
      - iModIntro.
        subst γ_'.
        iIntros (E E') "HE".
        iIntros (F F') "HF Hst".
        simpl.
        match goal with
        | |- context G [ofe_mor_car _ _ (`E) (ofe_mor_car _ _ Fun ?a)] =>
            set (f := a)
        end.
        iApply ("HE" $! (FunV f) with "[Hκ] HF Hst").
        iExists κ, κ'.
        iSplit.
        + subst f; iPureIntro.
          reflexivity.
        + iSplit; first done.
          iApply "Hκ".
      - subst γ_'.
        term_simpl.
        iApply "Hγ".
    }
    iSpecialize ("H" $! γ_ with "Hγ'").
    iSpecialize ("H" $! HOM_id END (compat_HOM_id _) m with "Hm Hst").
    iApply (wp_wand with "H").
    iIntros (_) "(H1 & (%w & %nm & %H2))".
    destruct nm as [a b].
    iModIntro.
    iFrame "H1".
    iExists w, ((a + 1)%nat, (b + 1)%nat).
    iPureIntro.
    term_simpl.
    eapply (steps_many _ _ _ 1 1 a b (a + 1)%nat (b + 1)%nat);
      [ lia | lia | apply Ceval_shift |].
    subst γ_'.
  Admitted.

  Lemma compat_nat {S : Set} (Γ : S → ty) n α :
    ⊢ valid Γ (interp_nat rs n) (LitV n) Tnat α α.
  Proof.
    iModIntro.
    iIntros (γ γ') "#Hγ".
    assert ((interp_nat rs n γ) = IT_of_V (RetV n)) as ->.
    { reflexivity. }
    iApply logrel_of_val.
    by iExists n.
  Qed.

  (* Lemma compat_recV {S : Set} (Γ : S -> ty) *)
  (*   τ1 α τ2 β e (e' : expr (inc (inc S))) : *)
  (*   ⊢ valid ((Γ ▹ (Tarr τ1 α τ2 β) ▹ τ1)) e e' τ2 α β *)
  (*     -∗ (∀ θ, valid Γ (interp_rec rs e) (RecV e') (Tarr τ1 α τ2 β) θ θ). *)
  (* Proof. *)
  (*   iIntros "#H". *)
  (*   iIntros (θ). *)
  (*   iModIntro. *)
  (*   iIntros (γ γ') "#Hγ". *)
  (*   set (f := (ir_unf rs e γ)). *)
  (*   iAssert (interp_rec rs e γ ≡ IT_of_V $ FunV (Next f))%I as "Hf". *)
  (*   { iPureIntro. apply interp_rec_unfold. } *)
  (*   iRewrite "Hf". *)
  (*   Opaque IT_of_V. *)
  (*   iApply logrel_of_val; term_simpl. *)
  (*   iExists _. iSplit. *)
  (*   { iPureIntro. apply into_val. } *)
  (*   iModIntro. *)
  (*   iLöb as "IH". *)
  (*   iIntros (v) "#Hw". *)
  (*   iIntros (κ) "#Hκ". *)
  (*   iIntros (σ) "Hσ Hst". *)
  (*   rewrite APP_APP'_ITV APP_Fun laterO_map_Next -Tick_eq. *)
  (*   pose (γ' := *)
  (*           (extend_scope (extend_scope γ (interp_rec rs e γ)) (IT_of_V v))). *)
  (*   rewrite /logrel. *)
  (*   Opaque extend_scope. *)
  (*   simpl. *)
  (*   rewrite hom_tick. *)
  (*   rewrite hom_tick. *)
  (*   iApply wp_tick. *)
  (*   iNext. *)
  (*   iSpecialize ("H" $! γ' with "[Hw]"). *)
  (*   { *)
  (*     iIntros (x). *)
  (*     destruct x as [| [| x]]; iIntros (ξ); iModIntro. *)
  (*     * iApply logrel_of_val. *)
  (*       iApply "Hw". *)
  (*     * iIntros (κ') "Hκ'". *)
  (*       iIntros (σ') "Hσ' Hst". *)
  (*       Transparent extend_scope. *)
  (*       simpl. *)
  (*       iRewrite "Hf". *)
  (*       iSpecialize ("Hκ'" $! (FunV (Next f)) with "[IH]"). *)
  (*       { *)
  (*         iExists (Next f). *)
  (*         iSplit; first done. *)
  (*         iModIntro. *)
  (*         iIntros (βv) "Hβv". *)
  (*         iIntros (κ'') "Hκ''". *)
  (*         iIntros (σ'') "Hσ'' Hst". *)
  (*         iApply ("IH" $! βv with "Hβv Hκ'' Hσ'' Hst"). *)
  (*       } *)
  (*       iApply ("Hκ'" $! σ' with "Hσ' Hst"). *)
  (*     * iApply "Hγ". *)
  (*   } *)
  (*   subst γ'. *)
  (*   iApply ("H" with "Hκ Hσ Hst"). *)
  (* Qed. *)

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
    D E F e1 e2 (e1' e2' : exprO S) op :
    ⊢ valid Γ e1 e1' Tnat E F
      -∗ valid Γ e2 e2' Tnat F D
      -∗ valid Γ (interp_natop rs op e1 e2) (NatOp op e1' e2') Tnat E D.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ γ') "#Hγ".
    iIntros (κ κ') "#Hκ".
    iIntros (m m') "Hm Hst".
    rewrite /interp_natop //=.

    set (K' := (NatOpRSCtx_HOM op e1 γ)).
    assert ((NATOP (do_natop op) (e1 γ) (e2 γ)) = ((`K') (e2 γ))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ K')). rewrite (HOM_compose_ccompose κ K' sss)//.

    iSpecialize ("G" $! γ with "Hγ").
    iSpecialize ("G" $! sss).    
    iSpecialize ("G" with "[H] Hm Hst").
    {
      iIntros (w w').
      iModIntro.
      iIntros "#Hw".
      iIntros (M M') "Hm Hst".
      subst sss.
      subst K'.
      simpl.

      pose (K' := (NatOpLSCtx_HOM op (IT_of_V w) γ _)).
      assert ((NATOP (do_natop op) (e1 γ) (IT_of_V w)) = ((`K') (e1 γ)))
        as -> by done.
      rewrite HOM_ccompose.
      pose (sss := (HOM_compose κ K')). rewrite (HOM_compose_ccompose κ K' sss)//.

      iSpecialize ("H" $! γ with "Hγ").
      iSpecialize ("H" $! sss).
      iSpecialize ("H" with "[] Hm Hst").
      {
        iIntros (v v').
        iModIntro.
        iIntros "#Hv".
        iIntros (m'' M'') "Hm Hst".
        subst sss.
        subst K'.
        simpl.

        iDestruct "Hw" as "(%n & #HEQ1 & #HEQ1')".
        iDestruct "Hv" as "(%n' & #HEQ2 & #HEQ2')".
        iSpecialize ("Hκ" $! (RetV (do_natop op n' n)) with "[]").
        {
          iExists _.
          iPureIntro.
          split; reflexivity.
        }
        iSpecialize ("Hκ" $! m'' with "Hm Hst").
        rewrite IT_of_V_Ret.

        iAssert ((NATOP (do_natop op) (IT_of_V v) (IT_of_V w))
                   ≡ (Ret (do_natop op n' n)))%I as "#HEQ".
        {
          iRewrite "HEQ1".
          rewrite IT_of_V_Ret.
          iAssert ((IT_of_V v) ≡ IT_of_V (RetV n'))%I as "#HEQ2''".
          {
            iApply f_equivI.
            iApply "HEQ2".
          }
          rewrite IT_of_V_Ret.
          iAssert (NATOP (do_natop op) (IT_of_V v) (Ret n)
                     ≡ NATOP (do_natop op) (Ret n') (Ret n))%I as "#HEQ2'''".
          {
            unshelve iApply (f_equivI (λne x, NATOP (do_natop op) x (Ret n))).
            { solve_proper. }
            { solve_proper. }
            iApply "HEQ2''".
          }
          iRewrite "HEQ2'''".
          rewrite NATOP_Ret.
          done.
        }
        iRewrite "HEQ".
        iApply (wp_wand with "Hκ").
        iIntros (_) "(H1 & (%t & %nm & H2))".
        iModIntro.
        iFrame "H1".
        iRewrite "HEQ2'".
        admit.
      }
      iApply (wp_wand with "H").
      iIntros (_) "(H1 & (%t & %nm & H2))".
      iModIntro.
      iFrame "H1".
      admit.
    }
    iApply (wp_wand with "G").
    iIntros (_) "(H1 & (%t & %nm & H2))".
    iModIntro.
    iFrame "H1".
    admit.
  Admitted.

  (* Lemma compat_app {S : Set} (Γ : S → ty) *)
  (*   ξ α β δ η τ e1 e2 : *)
  (*   ⊢ valid Γ e1 (Tarr η α τ β) ξ δ *)
  (*     -∗ valid Γ e2 η β ξ *)
  (*     -∗ valid Γ (interp_app rs e1 e2) τ α δ. *)
  (* Proof. *)
  (*   iIntros "#H #G". *)
  (*   iModIntro. *)
  (*   iIntros (γ) "#Hγ". *)
  (*   iIntros (κ) "#Hκ". *)
  (*   iIntros (σ) "Hσ Hst". *)
  (*   rewrite /interp_app //=. *)

  (*   pose (κ' := (AppLSCtx_HOM e2 γ)). *)
  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] => *)
  (*       set (F := b) *)
  (*   end. *)
  (*   assert (LET (e1 γ) F = ((`κ') (e1 γ))) as ->. *)
  (*   { simpl; unfold AppLSCtx. reflexivity. } *)
  (*   clear F. *)
  (*   assert ((`κ) ((`κ') (e1 γ)) = ((`κ) ◎ (`κ')) (e1 γ)) as ->. *)
  (*   { reflexivity. } *)
  (*   pose (sss := (HOM_compose κ κ')). *)
  (*   assert ((`κ ◎ `κ') = (`sss)) as ->. *)
  (*   { reflexivity. } *)

  (*   iSpecialize ("H" $! γ with "Hγ"). *)
  (*   iSpecialize ("H" $! sss). *)
  (*   iApply ("H" with "[H] Hσ Hst"). *)

  (*   iIntros (w). *)
  (*   iModIntro. *)
  (*   iIntros "#Hw". *)
  (*   iIntros (m') "Hm Hst". *)
  (*   subst sss. *)
  (*   subst κ'. *)
  (*   simpl. *)
  (*   rewrite LET_Val. *)
  (*   cbn [ofe_mor_car]. *)

  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] => *)
  (*       set (F := b) *)
  (*   end. *)
  (*   pose (κ'' := exist _ (LETCTX F) (LETCTX_Hom F) : HOM). *)
  (*   assert (((`κ) (LET (e2 γ) F)) = (((`κ) ◎ (`κ'')) (e2 γ))) as ->. *)
  (*   { reflexivity. } *)
  (*   pose (sss := (HOM_compose κ κ'')). *)
  (*   assert ((`κ ◎ `κ'') = (`sss)) as ->. *)
  (*   { reflexivity. } *)
  (*   iSpecialize ("G" $! γ with "Hγ"). *)
  (*   iSpecialize ("G" $! sss). *)
  (*   iApply ("G" with "[H] Hm Hst"). *)
  (*   iIntros (v). *)
  (*   iModIntro. *)
  (*   iIntros "#Hv". *)
  (*   iIntros (m'') "Hm Hst". *)
  (*   subst sss. *)
  (*   subst κ''. *)
  (*   simpl. *)
  (*   rewrite LET_Val. *)
  (*   subst F. *)
  (*   cbn [ofe_mor_car]. *)

  (*   iDestruct "Hw" as "(%n' & #HEQ & Hw)". *)
  (*   iSpecialize ("Hw" $! v with "Hv"). *)
  (*   iSpecialize ("Hw" $! κ with "Hκ"). *)
  (*   iSpecialize ("Hw" $! m'' with "Hm Hst"). *)
  (*   iAssert ((IT_of_V w ⊙ (IT_of_V v)) *)
  (*              ≡ (Fun n' ⊙ (IT_of_V v)))%I as "#HEQ'". *)
  (*   { *)
  (*     iApply (f_equivI (λne x, (x ⊙ (IT_of_V v)))). *)
  (*     iApply "HEQ". *)
  (*   } *)
  (*   iRewrite "HEQ'". *)
  (*   iApply "Hw". *)
  (* Qed. *)

  (* Lemma compat_appcont {S : Set} (Γ : S -> ty) e1 e2 τ α δ β σ : *)
  (*   valid Γ e1 (Tcont τ α) σ δ *)
  (*   -∗ valid Γ e2 τ δ β *)
  (*   -∗ valid Γ (interp_app_cont _ e1 e2) α σ β. *)
  (* Proof. *)
  (*   iIntros "#H #G". *)
  (*   iModIntro. *)
  (*   iIntros (γ) "#Henv". *)
  (*   iIntros (κ) "#Hκ". *)
  (*   iIntros (σ') "Hm Hst". *)

  (*   pose (κ' := (AppContRSCtx_HOM e1 γ)). *)
  (*   assert ((interp_app_cont rs e1 e2 γ) = ((`κ') (e2 γ))) as ->. *)
  (*   { simpl. reflexivity. } *)
  (*   assert ((`κ) ((`κ') (e2 γ)) = ((`κ) ◎ (`κ')) (e2 γ)) as ->. *)
  (*   { reflexivity. } *)
  (*   pose (sss := (HOM_compose κ κ')). *)
  (*   assert ((`κ ◎ `κ') = (`sss)) as ->. *)
  (*   { reflexivity. } *)

  (*   iSpecialize ("G" $! γ with "Henv"). *)
  (*   iSpecialize ("G" $! sss). *)
  (*   iApply ("G" with "[H] Hm Hst"). *)

  (*   iIntros (w). *)
  (*   iModIntro. *)
  (*   iIntros "#Hw". *)
  (*   iIntros (m') "Hm Hst". *)
  (*   subst sss. *)
  (*   subst κ'. *)
  (*   Opaque interp_app_cont. *)
  (*   simpl. *)

  (*   pose (κ'' := (AppContLSCtx_HOM (IT_of_V w) γ _)). *)
  (*   set (F := (`κ) _). *)
  (*   assert (F ≡ (((`κ) ◎ (`κ'')) (e1 γ))) as ->. *)
  (*   { *)
  (*     subst F. simpl. Transparent interp_app_cont. simpl. *)
  (*     f_equiv. *)
  (*     rewrite ->2 get_val_ITV. *)
  (*     simpl. *)
  (*     reflexivity. *)
  (*   } *)
  (*   pose (sss := (HOM_compose κ κ'')). *)
  (*   assert ((`κ ◎ `κ'') = (`sss)) as ->. *)
  (*   { reflexivity. } *)

  (*   iSpecialize ("H" $! γ with "Henv"). *)
  (*   iSpecialize ("H" $! sss). *)
  (*   iApply ("H" with "[] Hm Hst"). *)

  (*   iIntros (v). *)
  (*   iModIntro. *)
  (*   iIntros "#Hv". *)
  (*   iIntros (m'') "Hm Hst". *)
  (*   subst sss. *)
  (*   subst κ''. *)
  (*   Opaque APP_CONT. *)
  (*   simpl. *)

  (*   rewrite get_val_ITV. *)
  (*   simpl. *)

  (*   iDestruct "Hv" as "(%n' & #HEQ & #Hv)". *)
  (*   iRewrite "HEQ". *)
  (*   rewrite get_fun_fun. *)
  (*   simpl. *)

  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ *)
  (*                    (ofe_mor_car _ _ APP_CONT ?a) ?b] => *)
  (*       set (T := APP_CONT a b) *)
  (*   end. *)
  (*   iAssert (𝒫 ((`κ) T) ≡ (𝒫 ◎ (`κ)) T)%I as "HEQ'". *)
  (*   { iPureIntro. reflexivity. } *)
  (*   iRewrite "HEQ'"; iClear "HEQ'". *)
  (*   subst T. *)

  (*   iApply (wp_app_cont with "[Hst]"). *)
  (*   { reflexivity. } *)
  (*   - iFrame "Hst". *)
  (*   - simpl. *)
  (*     iNext. *)
  (*     iIntros "_ Hst". *)
  (*     rewrite later_map_Next. *)
  (*     rewrite <-Tick_eq. *)
  (*     iApply wp_tick. *)
  (*     iNext. *)
  (*     iSpecialize ("Hv" $! w with "Hw"). *)

  (*     iApply ("Hv" $! (laterO_map (𝒫 ◎ `κ) :: m'') with "[Hm] Hst"). *)
  (*     { *)
  (*       iIntros (p) "#Hp Hst". *)
  (*       iApply (wp_pop_cons with "Hst"). *)
  (*       iNext. *)
  (*       iIntros "_ Hst". *)
  (*       iApply ("Hκ" with "Hp Hm Hst"). *)
  (*     } *)
  (* Qed. *)

  (* Lemma compat_if {S : Set} (Γ : S -> ty) e e₁ e₂ τ σ α β : *)
  (*       ⊢ valid Γ e Tnat β α *)
  (*         -∗ valid Γ e₁ τ σ β *)
  (*         -∗ valid Γ e₂ τ σ β *)
  (*         -∗ valid Γ (interp_if rs e e₁ e₂) τ σ α. *)
  (* Proof. *)
  (*   iIntros "#H #G #J". *)
  (*   iModIntro. *)
  (*   iIntros (γ) "#Henv". *)
  (*   iIntros (κ) "#Hκ". *)
  (*   iIntros (σ') "Hm Hst". *)
  (*   unfold interp_if. *)
  (*   cbn [ofe_mor_car]. *)
  (*   pose (κ' := (IFSCtx_HOM (e₁ γ) (e₂ γ))). *)
  (*   assert ((IF (e γ) (e₁ γ) (e₂ γ)) = ((`κ') (e γ))) as -> by reflexivity. *)
  (*   assert ((`κ) ((`κ') (e γ)) = ((`κ) ◎ (`κ')) (e γ)) *)
  (*     as -> by reflexivity. *)
  (*   pose (sss := (HOM_compose κ κ')). *)
  (*   rewrite (HOM_compose_ccompose κ κ' sss)//. *)

  (*   iSpecialize ("H" $! γ with "Henv"). *)
  (*   iSpecialize ("H" $! sss). *)
  (*   iApply ("H" with "[] Hm Hst"). *)

  (*   iIntros (v). *)
  (*   iModIntro. *)
  (*   iIntros "#Hv". *)
  (*   iIntros (σ'') "Hm Hst". *)
  (*   iDestruct "Hv" as "(%n & #Hv)". *)
  (*   iRewrite "Hv". *)
  (*   rewrite IT_of_V_Ret. *)
  (*   subst sss. *)
  (*   subst κ'. *)
  (*   simpl. *)
  (*   unfold IFSCtx. *)
  (*   destruct (decide (0 < n)) as [H|H]. *)
  (*   - rewrite IF_True//. *)
  (*     iApply ("G" $! γ with "Henv [Hκ] Hm Hst"). *)
  (*     iIntros (w). *)
  (*     iModIntro. *)
  (*     iIntros "#Hw". *)
  (*     iIntros (σ''') "Hm Hst". *)
  (*     iApply ("Hκ" with "Hw Hm Hst"). *)
  (*   - rewrite IF_False//; last lia. *)
  (*     iApply ("J" $! γ with "Henv [Hκ] Hm Hst"). *)
  (*     iIntros (w). *)
  (*     iModIntro. *)
  (*     iIntros "#Hw". *)
  (*     iIntros (σ''') "Hm Hst". *)
  (*     iApply ("Hκ" with "Hw Hm Hst"). *)
  (* Qed. *)

  Open Scope types.

  Lemma fundamental_expr {S : Set} (Γ : S -> ty) τ α β e :
    Γ; α ⊢ₑ e : τ; β → ⊢ valid Γ (interp_expr rs e) e τ α β
  with fundamental_val {S : Set} (Γ : S -> ty) τ α β v :
    Γ; α ⊢ᵥ v : τ; β → ⊢ valid Γ (interp_val rs v) v τ α β.
  Proof.
    - intros H.
      destruct H.
      + by apply fundamental_val.
      + subst; iApply compat_var.
      + (* iApply compat_app; *)
      (*   by iApply fundamental_expr. *)
        admit.
      + (* iApply compat_appcont; *)
      (*   by iApply fundamental_expr. *)
        admit.
      + iApply compat_nat_op;
          by iApply fundamental_expr.
      + (* iApply compat_if; *)
      (*   by iApply fundamental_expr. *)
        admit.
      + iApply compat_shift;
          by iApply fundamental_expr.
      + iApply (compat_reset with "[]");
          by iApply fundamental_expr.
    - intros H.
      destruct H.
      + iApply compat_nat.
      + (* iApply (compat_recV with "[]"); *)
        (*   by iApply fundamental_expr. *)
        admit.
  Admitted.

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

Local Definition rs : gReifiers CtxDep 1 :=
  gReifiers_cons reify_delim gReifiers_nil.

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logrel_nat_adequacy  Σ `{!invGpreS Σ} `{!statePreG rs natO Σ} {S}
  (α : IT (gReifiers_ops rs) natO)
  (e : expr S) (n : nat) σ' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs natO Σ},
     (⊢ logrel rs Tnat Tnat Tnat α e)%I) →
  ssteps (gReifiers_sReifier rs) (𝒫 α) ([], ()) (Ret n) σ' k →
  ∃ m, steps (Cexpr e) (Cret (LitV n)) m.
Proof.
  intros Hlog Hst.
  pose (ϕ := λ (βv : ITV (gReifiers_ops rs) natO),
          ∃ m, steps (Cexpr e) (Cret $ κ βv) m).
  cut (ϕ (RetV n)).
  {
    destruct 1 as ( m' & Hm).
    exists m'. revert Hm. by rewrite κ_Ret.
  }
  eapply (wp_adequacy 0); eauto.
  Unshelve.
  2: {
    intros ?.
    apply False.
  }
  intros Hinv1 Hst1.
  pose (Φ := (λ (βv : ITV (gReifiers_ops rs) natO),
                ∃ n, interp_ty rs (Σ := Σ) (S := S) Tnat βv (LitV n)
                     ∗ ⌜∃ m, steps (Cexpr e) (Cret $ LitV n) m⌝)%I).
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
    iPoseProof (Hlog _ _) as "Hlog".
    iAssert (has_substate _)%I with "[Hs]" as "Hs".
    {
      unfold has_substate, has_full_state.
      admit.
    }
    iSpecialize ("Hlog" $! HOM_id END (compat_HOM_id _ _) [] [] with "[]"). 
    {
      iIntros (αv v) "HHH GGG".
      iApply (wp_pop_end with "GGG").
      iNext.
      iIntros "_ GGG".
      iApply wp_val.
      iModIntro.
      iFrame "GGG".
      iExists v, (1, 1).
      iPureIntro.
      eapply (steps_many _ _ _ 0 0 1 1 1 1);
        [done | done | apply Ceval_val |].
      eapply (steps_many _ _ _ 0 0 1 1 1 1);
        [done | done | apply Ccont_end |].
      eapply (steps_many _ _ _ 1 1 0 0 1 1);
        [done | done | apply Cmcont_ret |].
      constructor.
    }
    simpl.
    unfold obs_ref'.
    iSpecialize ("Hlog" with "Hs").
    iApply (wp_wand with "Hlog").
    iIntros ( βv). iIntros "H".
    iDestruct "H" as "[Hi Hsts]".
    subst Φ.
    admit.
Admitted.

Theorem adequacy (e : expr ∅) (k : nat) σ' n :
  (typed_expr empty_env Tnat e Tnat Tnat) →
  ssteps (gReifiers_sReifier rs) (𝒫 (interp_expr rs e ı_scope)) ([], ())
    (Ret k : IT _ natO) σ' n →
  ∃ mm, steps (Cexpr e) (Cret $ LitV k) mm.
Proof.
  intros Hty Hst.
  pose (Σ := gFunctors.app invΣ (gFunctors.app (stateΣ rs natO) gFunctors.nil)).
  eapply (logrel_nat_adequacy Σ (interp_expr rs e ı_scope)); last eassumption.
  intros ? ?.
  iPoseProof (fundamental_expr rs _ _ _ _ _ Hty) as "#H".
  unfold valid.
  unshelve iSpecialize ("H" $! ı_scope _ with "[]").
  { apply ı%bind. }
  { iIntros (x); destruct x. }
  rewrite ebind_id; first last.
  { intros ?; reflexivity. }
  iApply "H".
Qed.
