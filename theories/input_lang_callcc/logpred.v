(** Unary (Kripke) logical relation for the IO lang *)
From Equations Require Import Equations.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang_callcc Require Import lang interp.
Require Import gitrees.lang_generic_sem.
Require Import Binding.Lib Binding.Set Binding.Env.

Section io_lang.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{SO : !SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ, !na_invG Σ}.
  Notation iProp := (iProp Σ).

  Variable s : stuckness.
  Context {A:ofe}.
  Variable (P : A → iProp).
  Context `{!NonExpansive P}.

  Local Notation expr_pred := (expr_pred s rs P).

  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n : nat, αv ≡ RetV n)%I.
  Solve All Obligations with solve_proper.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) := λne αv,
    (□ ∀ σ βv, has_substate σ -∗
               Φ1 βv -∗
               expr_pred (IT_of_V αv ⊙ (IT_of_V βv)) (λne v, ∃ σ', Φ2 v ∗ has_substate σ'))%I.
  Solve All Obligations with solve_proper.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | Tnat => interp_tnat
    | Tarr τ1 τ2 => interp_tarr (interp_ty τ1) (interp_ty τ2)
    | Tcont τ => interp_tarr (interp_ty τ) (constO ((False)%I))
    end.

  Program Definition ı_scope
    : @interp_scope F R _ ∅ := λne x, match x with end.

  Definition ssubst_valid {ty} (interp_ty : ty → ITV -n> iProp) {S : Set} (Γ : S -> ty) (ss : interp_scope S) : iProp :=
    (∀ x, □ expr_pred (ss x) (interp_ty (Γ x)))%I.

  #[global] Instance io_lang_interp_ty_pers  τ βv : Persistent (io_lang.interp_ty τ βv).
  Proof. induction τ; apply _. Qed.
  #[global] Instance ssubst_valid_pers {S : Set} (Γ : S -> ty) ss : Persistent (ssubst_valid interp_ty Γ ss).
  Proof.
    apply _.
  Qed.

  Program Definition valid1 {S : Set} (Γ : S -> ty) (α : @interp_scope F R _ S -n> IT) (τ : ty) : iProp :=
    (∀ σ ss, has_substate σ -∗ ssubst_valid interp_ty Γ ss -∗
    expr_pred (α ss) (λne v, ∃ σ', interp_ty τ v ∗ has_substate σ'))%I.
  Solve Obligations with solve_proper.
    
  Lemma compat_nat {S : Set} n (Ω : S -> ty) :
    ⊢ valid1 Ω (interp_nat rs n) Tnat.
  Proof.
    iIntros (σ αs) "Hs Has".
    simpl. iApply expr_pred_ret. simpl.
    eauto with iFrame.
  Qed.
  Lemma compat_var {S : Set} Ω τ (v : S) :
    Ω v = τ →
    ⊢ valid1 Ω (interp_var v) τ.
  Proof.
    intros Hv.
    iIntros (σ ss) "Hs Has". simpl.
    iIntros (x) "G".
    iDestruct ("Has" $! v x with "G") as "Has".
    iApply (wp_wand with "[$Has] [Hs]").
    iIntros (v') "(%y & H1 & H2)".
    iModIntro.
    iExists y.
    iFrame "H2".
    iExists σ.
    subst.
    iFrame.
  Qed.
  
  Lemma compat_if {S : Set} (Γ : S -> ty) τ α β1 β2 :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β1 τ -∗
      valid1 Γ β2 τ -∗
      valid1 Γ (interp_if rs α β1 β2) τ.
  Proof.
    iIntros "H0 H1 H2".
    iIntros (σ ss) "Hs #Has".
    iSpecialize ("H0" with "Hs Has").
    simpl.
    iApply (expr_pred_bind (IFSCtx _ _) with "H0").
    iIntros (αv) "Ha/=".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Hn".
    unfold IFSCtx. iIntros (x) "Hx".
    iRewrite "Hn".
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply ("H2" with "Hs Has Hx").
    - rewrite IF_True; last lia.
      iApply ("H1" with "Hs Has Hx").
  Qed.
  
  Lemma compat_input {S : Set} (Γ : S -> ty) :
    ⊢ valid1 Γ (interp_input rs) Tnat.
  Proof.
    iIntros (σ ss) "Hs #Has".
    iApply expr_pred_frame.
    destruct (update_input σ) as [n σ'] eqn:Hinp.
    iApply (wp_input with "Hs") .
    { eauto. }
    iNext. iIntros "_ Hs".
    iApply wp_val. simpl. eauto with iFrame.
  Qed.

  Lemma compat_output {S : Set} (Γ : S -> ty) α :
    ⊢ valid1 Γ α Tnat → valid1 Γ (interp_output rs α) Tnat.
  Proof.
    iIntros "H".
    iIntros (σ ss) "Hs #Has".
    iSpecialize ("H" with "Hs Has").
    simpl.
    iApply (expr_pred_bind (get_ret _) with "H").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ') "[Ha Hs]".
    iDestruct "Ha" as (n) "Hn".
    iApply expr_pred_frame.
    iRewrite "Hn".
    rewrite get_ret_ret.
    iApply (wp_output with "Hs").
    { reflexivity. }
    iNext. iIntros "_ Hs /=".
    eauto with iFrame.
  Qed.
  
  Lemma compat_app {S : Set} (Γ : S -> ty) α β τ1 τ2 :
    ⊢ valid1 Γ α (Tarr τ1 τ2) -∗
      valid1 Γ β τ1 -∗
      valid1 Γ (interp_app rs α β) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (σ ss) "Hs #Has". simpl.
    iSpecialize ("H2" with "Hs Has").
    iApply (expr_pred_bind (AppRSCtx _) with "H2").
    iIntros (βv) "Hb/=".
    iDestruct "Hb" as (σ') "[Hb Hs]".
    unfold AppRSCtx.
    iSpecialize ("H1" with "Hs Has").
    iApply (expr_pred_bind (AppLSCtx (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ'') "[Ha Hs]".
    unfold AppLSCtx.
    iApply ("Ha" with "Hs Hb").
  Qed.

  Lemma compat_rec {S : Set} (Γ : S -> ty) τ1 τ2 α :
    ⊢ □ valid1 ((Γ ▹ (Tarr τ1 τ2) ▹ τ1)) α τ2 -∗
      valid1 Γ (interp_rec rs α) (Tarr τ1 τ2).
  Proof.
    iIntros "#H". iIntros (σ ss) "Hs #Hss".
    pose (env := ss). fold env.    
    pose (f := (ir_unf rs α env)).
    iAssert (interp_rec rs α env ≡ IT_of_V $ FunV (Next f))%I as "Hf".
    { iPureIntro. apply interp_rec_unfold. }
    iRewrite "Hf". iApply expr_pred_ret. simpl.
    iExists _. iFrame. iModIntro.
    iLöb as "IH". iSimpl.
    clear σ.
    iIntros (σ βv) "Hs #Hw".
    iIntros (x) "Hx".
    iApply wp_lam.
    iNext.
    unfold valid1.
    iAssert (IT_of_V (FunV (Next f)) ≡ interp_rec rs α env)%I as "Heq".
    { rewrite interp_rec_unfold. done. }    
    iRewrite -"Heq".
    unfold f.
    Opaque extend_scope.
    simpl.
    pose (ss' := (extend_scope (extend_scope env (interp_rec rs α env)) (IT_of_V βv))).
    iApply ("H" with "[$Hs] [] [$Hx]").
    Transparent extend_scope.
    iIntros (x'); destruct x' as [| [| x']]; simpl.
    - iModIntro.
      by iApply expr_pred_ret.
    - iModIntro.
      iRewrite - "Heq".
      iApply expr_pred_ret.
      iModIntro.
      iApply "IH".
    - iApply "Hss".
  Qed.

  Lemma compat_natop {S : Set} (Γ : S -> ty) op α β :
    ⊢ valid1 Γ α Tnat -∗
      valid1 Γ β Tnat -∗
      valid1 Γ (interp_natop _ op α β) Tnat.
  Proof.
    iIntros "H1 H2".
    iIntros (σ ss) "Hs #Has". simpl.
    iSpecialize ("H2" with "Hs Has").
    iApply (expr_pred_bind (NatOpRSCtx _ _) with "H2").
    iIntros (βv) "Hb/=".
    iDestruct "Hb" as (σ') "[Hb Hs]".
    unfold NatOpRSCtx.
    iSpecialize ("H1" with "Hs Has").
    iApply (expr_pred_bind (NatOpLSCtx _ (IT_of_V βv)) with "H1").
    iIntros (αv) "Ha".
    iDestruct "Ha" as (σ'') "[Ha Hs]".
    unfold NatOpLSCtx.
    iDestruct "Hb" as (n1) "Hb".
    iDestruct "Ha" as (n2) "Ha".
    iRewrite "Hb". iRewrite "Ha".
    simpl. iApply expr_pred_frame.
    rewrite NATOP_Ret. iApply wp_val. simpl.
    eauto with iFrame.
  Qed.

  Lemma compat_throw {S : Set} (Γ : S -> ty) τ τ' α β :
    ⊢ valid1 Γ α τ -∗
      valid1 Γ β (Tcont τ) -∗
      valid1 Γ (interp_throw _ α β) τ'.
  Proof.
  Admitted.
    
  Lemma compat_callcc {S : Set} (Γ : S -> ty) τ α :
    ⊢ valid1 (Γ ▹ Tcont τ) α τ -∗
      valid1 Γ (interp_callcc _ α) τ.
  Proof.
  Admitted.
    
  Lemma fundamental {S : Set} (Γ : S -> ty) e τ :
    typed Γ e τ → ⊢ valid1 Γ (interp_expr rs e) τ
  with fundamental_val {S : Set} (Γ : S -> ty) v τ :
    typed_val Γ v τ → ⊢ valid1 Γ (interp_val rs v) τ.
  Proof.
    - destruct 1.
      + by iApply fundamental_val.
      + by iApply compat_var.
      + iApply compat_app; iApply fundamental; eauto.
      + iApply compat_natop; iApply fundamental; eauto.
      + iApply compat_if;  iApply fundamental; eauto.
      + iApply compat_input.
      + iApply compat_output; iApply fundamental; eauto.
      + iApply compat_throw; iApply fundamental; eauto.
      + iApply compat_callcc; iApply fundamental; eauto.
    - destruct 1.
      + iApply compat_nat.
      + iApply compat_rec; iApply fundamental; eauto.
  Qed.
  
  Lemma fundmanetal_closed (e : expr ∅) (τ : ty) :
    typed □ e τ →
    ⊢ valid1 □ (interp_expr rs e) τ.
  Proof. apply fundamental. Qed.
  
End io_lang.

Arguments interp_ty {_ _ _ _ _ _ _ _ _ _ _ _} τ.
Arguments interp_tarr {_ _ _ _ _ _ _ _ _ _ _} Φ1 Φ2.

Local Definition rs : gReifiers _ := gReifiers_cons reify_io gReifiers_nil.

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

(* Check IT_of_to_V. *)
(* Search SetoidClass.Setoid. *)

(* Lemma logpred_adequacy (* cr *) (* Σ *) R `{!Cofe R(* , SubOfe natO R *)} (* `{!invGpreS Σ} `{!statePreG rs R Σ} *) (* τ *) *)
(*   (* (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R) *) *)
(*   (β : @IT (gReifiers_ops rs) R _) (* st st' k *) : *)
(*   (* (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ}, *) *)
(*   (*     (£ cr ⊢ valid1 rs notStuck (λ _:unitO, True)%I □ α τ)%I) → *) *)
(*   (* ssteps (gReifiers_sReifier rs) (α (@ı_scope _ rs R _)) st β st' k → *) *)
(*   (* (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1) *) *)
(*   (*  ∨ *) (∃ βv, IT_of_V βv ≡ β). *)
(* (* Proof. *) *)
(* (*   intros Hlog Hst. *) *)
(* (*   destruct (IT_to_V β) as [βv|] eqn:Hb. *) *)
(* (*   { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. } *) *)
(* (*   left. *) *)
(* (*   cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1) *) *)
(* (*       ∨ (∃ e, β ≡ Err e ∧ notStuck e)). *) *)
(* (*   { intros [?|He]; first done. *) *)
(* (*     destruct He as [? [? []]]. } *) *)
(* (*   eapply (wp_safety cr); eauto. *) *)
(* (*   { apply Hdisj. } *) *)
(* (*   { by rewrite Hb. } *) *)
(* (*   intros H1 H2. *) *)
(* (*   exists (interp_ty (s:=notStuck) (P:=(λ _:unitO, True)) τ)%I. split. *) *)
(* (*   { apply _. } *) *)
(* (*   iIntros "[Hcr  Hst]". *) *)
(* (*   iPoseProof (Hlog with "Hcr") as "Hlog". *) *)
(* (*   destruct st as [σ []]. *) *)
(* (*   iAssert (has_substate σ) with "[Hst]" as "Hs". *) *)
(* (*   { unfold has_substate, has_full_state. *) *)
(* (*     assert (of_state rs (IT (gReifiers_ops rs) _) (σ,()) ≡ *) *)
(* (*             of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state σ)) as ->; last done. *) *)
(* (*     intro j. unfold sR_idx. simpl. *) *)
(* (*     unfold of_state, of_idx. *) *)
(* (*     destruct decide as [Heq|]; last first. *) *)
(* (*     { inv_fin j; first done. *) *)
(* (*       intros i. inversion i. } *) *)
(* (*     inv_fin j; last done. *) *)
(* (*     intros Heq. *) *)
(* (*     rewrite (eq_pi _ _ Heq eq_refl)//. *) *)
(* (*   } *) *)
(* (*   iSpecialize ("Hlog" $! σ with "Hs []"). *) *)
(* (*   { iApply ssubst_valid_nil. } *) *)
(* (*   iSpecialize ("Hlog" $! tt with "[//]"). *) *)
(* (*   iApply (wp_wand with"Hlog"). *) *)
(* (*   iIntros ( βv). simpl. iDestruct 1 as (_) "[H _]". *) *)
(* (*   iDestruct "H" as (σ1') "[$ Hsts]". *) *)
(* (*   done. *) *)
(* (* Qed. *) *)

(* Lemma io_lang_safety e τ σ st' (β : IT (sReifier_ops (gReifiers_sReifier rs)) natO) k : *)
(*   typed empC e τ → *)
(*   ssteps (gReifiers_sReifier rs) (interp_expr _ e ()) (σ,()) β st' k → *)
(*   (∃ β1 st1, sstep (gReifiers_sReifier rs) β st' β1 st1) *)
(*    ∨ (∃ βv, IT_of_V βv ≡ β). *)
(* Proof. *)
(*   intros Htyped Hsteps. *)
(*   pose (Σ:=#[invΣ;stateΣ rs natO]). *)
(*   assert (invGpreS Σ). *)
(*   { apply _. } *)
(*   assert (statePreG rs natO Σ). *)
(*   { apply _. } *)
(*   eapply (logpred_adequacy 0 Σ); eauto. *)
(*   intros ? ?. iIntros "_". *)
(*   by iApply fundamental. *)
(* Qed. *)
