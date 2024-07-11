From gitrees.examples.except_lang Require Import lang.

Require Import Binding.Lib Binding.Set Binding.Env.
Require Import Coq.Program.Equality.


Module Typing (Errors : ExcSig).
  Module _LANG := Lang Errors.
  Import _LANG.
  Import _Exc.
  
  (** Bare types **)
  Inductive bty : Type :=
  | Bnat : bty
  | Barr : bty → bty → bty
  .


  (** Types indicating possible errors raised **)
  Inductive pty : Type :=
  | Tnat : pty
  | Tarr : pty → ty → pty
  with ty : Type :=
    Ty : pty → (exc → Prop) → ty.

  Context (ETy : exc → pty).
  Notation "'ℕ'" := Tnat.
  Notation "σ '⟶' τ" := (Tarr σ τ)
                          (at level 20).
  Notation "τ ⇑ E" := (Ty τ E)
                        (at level 20,
                           E at level 20,
                           no associativity).
  Notation "E1 ⪯ E2" := (∀ x, E1 x → E2 x)
                          (at level 20,
                             no associativity,
                          only parsing).

  Notation "⋆" := (λ _, False).

  Reserved Notation "τ '≲' σ"
    (at level 20).
  
  Reserved Notation "τ '⪍' σ"
    (at level 20).
  
  Inductive le_pty : pty → pty → Prop :=
  | Le_nat : ℕ ≲ ℕ
  | Le_arr τ1 τ2 σ1 σ2 :
    τ2 ≲ τ1 →
    σ1 ⪍ σ2 →
    (τ1 ⟶ σ1) ≲ (τ2 ⟶ σ2)
  with le_ty : ty → ty → Prop :=
    Le_Ty τ1 τ2 E1 E2 :
      τ1 ≲ τ2 →
      E1 ⪯ E2 →
      (τ1 ⇑ E1) ⪍ (τ2 ⇑ E2)
  where "τ ≲ σ" := (le_pty τ σ)
  and "τ ⪍ σ" := (le_ty τ σ).

  Notation "E1 ≋ E2" := (∀ x, E1 x ↔ E2 x)
                        (at level 20,
                           no associativity).
  
  Lemma le_set_trans {A} : ∀ (E1 E2 E3 : A → Prop), E1 ⪯ E2 → E2 ⪯ E3 → E1 ⪯ E3.
  Proof. eauto. Qed.

  Lemma le_set_refl {A} : ∀ (E : A → Prop), E ⪯ E.
  Proof. eauto. Qed.
          
  Lemma le_pty_trans : ∀ τ1 τ2 τ3, τ1 ≲ τ2 → τ2 ≲ τ3 → τ1 ≲ τ3
  with le_ty_trans : ∀ τ1 τ2 τ3, τ1 ⪍ τ2 → τ2 ⪍ τ3 → τ1 ⪍ τ3.
  Proof.
    - intros τ1 τ2.
      destruct τ2.
      + intros τ3 H1 H2.
        inversion H1. subst.
        inversion H2. subst.
        done.
      + intros τ3 H1 H2.
        inversion H1. subst.
        inversion H2. subst.
        constructor.
        * by eapply le_pty_trans.
        * by eapply le_ty_trans.
    - intros τ1 τ2 τ3 H1 H2.
      destruct τ1, τ2, τ3.
      inversion H1. subst.
      inversion H2. subst.
      constructor.
      + by eapply le_pty_trans.
      + by eapply le_set_trans.
  Qed.

  Lemma le_pty_refl : ∀ τ, τ ≲ τ
  with le_ty_refl : ∀ τ, τ ⪍ τ.
  Proof.
    - intros τ.
      destruct τ; constructor.
      + apply le_pty_refl.
      + apply le_ty_refl.
    - intros [τ E].
      constructor.
      + apply le_pty_refl.
      + apply le_set_refl.
  Qed.
  
  (** Compatibility between types and bare types **)

  Reserved Notation "τ ≅ σ"
    (at level 20).

  Reserved Notation "τ ≈ σ"
    (at level 20).

  Inductive compatp : bty → pty → Prop :=
  | Comp_nat : Bnat ≅ ℕ
  | Comp_arr σb σ τb τ : σb ≅ σ →
                         τb ≈ τ →
                         Barr σb τb ≅ (σ ⟶ τ)
  with compat : bty → ty → Prop :=
    Compat_Ty τb τ E : τb ≅ τ →
                       τb ≈ Ty τ E
  where "σ ≅ τ" := (compatp σ τ)
  and "σ ≈ τ" := (compat σ τ).
  
  Lemma le_ty_compat τ1 τ2 σ (Hsub : τ1 ⪍ τ2) : (σ ≈ τ1 ↔ σ ≈ τ2)
  with le_pty_compat τ1 τ2 σ (Hsub : τ1 ≲ τ2) : (σ ≅ τ1 ↔ σ ≅ τ2).
  Proof.
    - destruct τ1 as [τ1 E1].
      destruct τ2 as [τ2 E2].
      inversion Hsub. subst.
      split; constructor; inversion H; subst; by eapply (le_pty_compat τ1).
    - destruct τ1; inversion Hsub; subst; first done.
      split; intros Hsim; inversion Hsim; subst; constructor.
      + by eapply le_pty_compat.
      + by eapply (le_ty_compat t).
      + by eapply (le_pty_compat τ3).
      + by eapply (le_ty_compat t).
  Qed.
  
  Notation "E ⊕ e" := (λ x, x = e ∨ E x)
                        (at level 20).

  Notation "E ⊖ e" := (λ x, x <> e ∧ E x)
                        (at level 20).

  Notation "E1 ⊍ E2" := (λ x, E1 x ∨ E2 x)
                        (at level 20).
  
  Reserved Notation "Γ '⊢ₑ' e ':' τ"
    (at level 70
     , e at level 60
     , τ at level 20
     , no associativity
    ).
  
  Reserved Notation "Γ '⊢ᵥ' v : τ"
    (at level 70
     , v at level 60
     , τ at level 20
     , no associativity
    ).

  Inductive typed {S : Set} : (S → pty) → expr S → ty → Prop :=
  | typed_Var Γ E x τ : Γ x ≲ τ →
                        (Γ ⊢ₑ (Var x) : τ ⇑ E)
                          
  | typed_Lit Γ E v : (Γ ⊢ᵥ (LitV v) : ℕ ⇑ E)
                        
  | typed_Rec Γ E f σ τ α :
    (σ ⟶ τ) ≲ α→
    (Γ ▹ (σ ⟶ τ) ▹ σ ⊢ₑ f : τ) →
    (Γ ⊢ᵥ (RecV f) : α ⇑ E)
      
 (* | typed_wk Γ τ1 τ2 e :
      τ1 ⪍ τ2 →
      (Γ ⊢ₑ e : τ1) →
      (Γ ⊢ₑ e : τ2) *)
      
  | typed_App E E1 E2 E3 Γ f v σ τ :
    (E1 ⊍ E2 ⊍ E3) ⪯ E →
    (Γ ⊢ₑ f : (σ ⟶ (τ ⇑ E1)) ⇑ E2) →
    (Γ ⊢ₑ v : σ ⇑ E3) →
    (Γ ⊢ₑ App f v : τ ⇑ E)
      
  | typed_Op Γ E E1 E2 op l r :
    (E1 ⊍ E2) ⪯ E →
    (Γ ⊢ₑ l : ℕ ⇑ E1) →
    (Γ ⊢ₑ r : ℕ ⇑ E2) →
    (Γ ⊢ₑ NatOp op l r : ℕ ⇑ E)
      
  | typed_If Γ E E1 E2 E3 c t e τ :
    (E1 ⊍ E2 ⊍ E3) ⪯ E→
    (Γ ⊢ₑ c : ℕ ⇑ E1) →
    (Γ ⊢ₑ t : τ ⇑ E2) →
    (Γ ⊢ₑ e : τ ⇑ E3) →
    (Γ ⊢ₑ If c t e : τ ⇑ E)
      
  | typed_Throw Γ E1 E2 err v σ τ :
    σ ≲ ETy err →
    (E1 ⊕ err) ⪯ E2 → 
    (Γ ⊢ₑ v : σ ⇑ E1) → 
    (Γ ⊢ₑ Throw err v : τ ⇑ E2)
      
  | typed_Catch Γ E E1 E2 err h v σ τ :
    ETy err ≲ σ →
    (E1 ⊍ (E2 ⊖ err)) ⪯ E →
    (Γ ▹ σ ⊢ₑ h : τ ⇑ E1) →
    (Γ ⊢ₑ v : τ ⇑ E2) →
    (Γ ⊢ₑ Catch err v h : τ ⇑ E)
      
  where "Γ ⊢ₑ e : τ" := (typed Γ e τ)
  and "Γ ⊢ᵥ v : τ"  := (Γ ⊢ₑ (Val v) : τ).
  Print cont.
  Reserved Notation "Γ '⊢ₖ' K ':' σ ⇒ τ"
    (at level 70
     , K at level 60
     , σ at level 20
     , τ at level 20
     , no associativity
    ).

  
  Inductive typ_cont {S : Set} : (S → pty) → cont S → ty → ty → Prop :=
  (* | typed_Err_Wk E1 E2 E3 Γ e σ τ : E1 ⪯ E2 →
                                  (Γ ; E1 ⊢ₖ e : σ ; E3 ⇒ τ) →
                                  (Γ ; E2 ⊢ₖ e : σ ; E3 ⇒ τ) 
  | typed_Err_St E1 E2 E3 Γ e σ τ :  E3 ⪯ E2 →
                                  (Γ ; E1 ⊢ₖ e : σ ; E2 ⇒ τ) →
                                  (Γ ; E1 ⊢ₖ e : σ ; E3 ⇒ τ) *)
  | typed_END Γ τ1 τ2 : τ1 ⪍ τ2 →
                        (Γ ⊢ₖ END : τ1 ⇒ τ2)
  | typed_IfK Γ e₁ e₂ K E1 E2 E3 E4 τ σ :
    (E1 ⊍ E2 ⊍ E3) ⪯ E4 → 
    (Γ ⊢ₑ e₁ : σ ⇑ E2) → 
    (Γ ⊢ₑ e₂ : σ ⇑ E3) →
    (Γ ⊢ₖ K : σ ⇑ E4 ⇒ τ) →
    (Γ ⊢ₖ IfK e₁ e₂ K : ℕ ⇑ E1 ⇒ τ)
  | typed_AppLK Γ E1 E2 E3 E4 v K σ τ α :
    (E1 ⊍ E2 ⊍ E3) ⪯ E4 →
    (Γ ⊢ᵥ v : σ ⇑ E3) →
    (Γ ⊢ₖ K : τ ⇑ E4 ⇒ α) →
    (Γ ⊢ₖ AppLK v K : ((σ ⟶ (τ ⇑ E1)) ⇑ E2) ⇒ α)
  | typed_AppRK Γ E1 E2 E3 E4 e K σ τ α :
    (E1 ⊍ E2 ⊍ E3) ⪯ E4 → 
    (Γ ⊢ₑ e : (σ ⟶ (τ ⇑ E1)) ⇑ E2) →
    (Γ ⊢ₖ K : (τ ⇑ E4)  ⇒ α) →
    (Γ ⊢ₖ AppRK e K : (σ ⇑ E3) ⇒ α)
  | typed_NatOpLK Γ E1 E2 E3 op v K τ :
    (E1 ⊍ E2) ⪯ E3 → 
    (Γ ⊢ᵥ v : ℕ ⇑ E1) →
    (Γ ⊢ₖ K : (ℕ ⇑ E3) ⇒ τ) →
    (Γ ⊢ₖ NatOpLK op v K : (ℕ ⇑ E2) ⇒ τ)
  | typed_NatOpRK Γ E1 E2 E3 op e K τ :
    (E1 ⊍ E2) ⪯ E3 → 
    (Γ ⊢ₑ e : ℕ ⇑ E1) →
    (Γ ⊢ₖ K : ℕ ⇑ E3 ⇒ τ) →
    (Γ ⊢ₖ NatOpRK op e K : (ℕ ⇑ E2) ⇒ τ)
  | typed_ThrowK Γ E1 E2 err K σ τ α :
    σ ≲ ETy err →
    (E1 ⊕ err) ⪯ E2 → 
    (Γ ⊢ₖ K : (τ ⇑ E2)  ⇒ α) →
    (Γ ⊢ₖ ThrowK err K : (σ ⇑ E1) ⇒ α)
  | typed_CatchK Γ E1 E2 E3 err h K σ τ τ' α :
    ETy err ≲ σ →
    τ' ≲ τ →
    (E1 ⊍ (E2 ⊖ err)) ⪯ E3 →
    (Γ ▹ σ ⊢ₑ h : (τ ⇑ E1)) →
    (Γ ⊢ₖ K : (τ ⇑ E3) ⇒ α) →
    (Γ ⊢ₖ CatchK err h K : (τ' ⇑ E2) ⇒ α)

  where "Γ '⊢ₖ' K ':' σ ⇒ τ" := (typ_cont Γ K σ τ).
   
    
  Definition typedConfig {S : Set} (Γ : S → pty) (c : @config S) (τ : ty) : Prop :=
    match c with
    | Cexpr e => (Γ ⊢ₑ e : τ)
    | Ceval e K => (Γ ⊢ₑ (fill K e) : τ)
    | Ccont K v => (Γ ⊢ₑ (fill K (Val v)) : τ)
    | Cret v => (Γ ⊢ᵥ v : τ)
    end.
    
  Notation "Γ ⊢ᵢ c : τ" := (typedConfig Γ c τ)
                                (at level 70
                                 , c at level 60
                                 , τ at level 20
                                 , no associativity
                                ).
  
  Lemma weakening {S T : Set} :
    ∀ (Γ : S → pty) (Δ : T → pty) (δ : S [→] T) (e : expr S) τ,
    (Γ ⊢ₑ e : τ) →
    (Δ • δ ≡ Γ) →
    (Δ ⊢ₑ (fmap δ e) : τ).
   Proof.
    intros Γ Δ δ e τ Hty Hag.
    generalize dependent T.
    induction Hty; intros.
    + constructor. specialize (Hag x). simpl in Hag. rewrite Hag. done.
    + by constructor.
    + econstructor; first done.
      apply IHHty.
      intros [|[|]].
      1, 2 : done.
      simpl.
      apply Hag.
   (* + econstructor; try done.
      by apply IHHty. *)
    + eapply typed_App.
      * eauto.
      * by apply IHHty1.
      * by apply IHHty2.
    + econstructor.
      * eauto.
      * by apply IHHty1.
      * by apply IHHty2.
    + econstructor.
      * eauto.
      * by apply IHHty1.
      * by apply IHHty2.
      * by apply IHHty3.
    + eapply typed_Throw; try done.
      by apply IHHty.
    + econstructor; first done.
      * eauto.
      * apply IHHty1.
        intros [|]; first done.
        simpl. apply Hag.
      * by apply IHHty2.
   Qed.

 Lemma weakening_error {S : Set} :
    ∀ (Γ : S → pty) (e : expr S) σ τ,
    (Γ ⊢ₑ e : σ) →
    σ ⪍ τ →
    (Γ ⊢ₑ e : τ).
   Proof.
     intros Γ e [τ Eτ] σ Hty.
     generalize dependent σ.
    induction Hty; intros [σ' Eσ'] Hsub; inversion Hsub; subst.
    + constructor. by eapply le_pty_trans.
    + inversion H2. by constructor.
    + econstructor; first by eapply le_pty_trans. done.
   (*   intros [|[|]].
        1, 2 : done.
        simpl.
        apply Hag.
        + econstruct or; try done.
        by apply IHHty. *)
    + eapply typed_App.
      * eauto.
      * apply IHHty1.
        constructor; last eauto.
        constructor; first apply le_pty_refl.
        constructor; last apply le_set_refl.
        done.
      * apply IHHty2, le_ty_refl.
    + inversion H3. subst.
      econstructor.
      * eauto.
      * by apply IHHty1.
      * by apply IHHty2.
    + econstructor.
      * eauto.
      * apply IHHty1, le_ty_refl.
      * apply IHHty2.
        constructor; last apply le_set_refl.
        done.
      * by apply IHHty3.
    + eapply typed_Throw; try done.
      eauto.
    + econstructor; first done.
      * eauto.
      * apply IHHty1.
        constructor; last apply le_set_refl.
        done.
      * apply IHHty2.
        constructor; last apply le_set_refl.
        done.
   Qed.
(*
   
 Lemma weakening_sub {S: Set} :
    ∀ (Γ : S → pty) (Δ : S → pty) (e : expr S) τ,
    (Γ ⊢ₑ e : τ) →
    (∀ x, Δ x ≲ Γ x) →
    (Δ ⊢ₑ e : τ).
   Proof.
    intros Γ Δ e τ Hty Hag.
    induction Hty; intros.
    + constructor. eapply le_pty_trans; done.
    + by constructor.
    + constructor. apply IHHty.
      intros [|[|]].
      1, 2 : term_simpl; apply le_pty_refl.
      simpl.
      apply Hag.
    + econstructor; try done.
      by apply IHHty.
    + eapply typed_App.
      * by apply IHHty1.
      * by apply IHHty2.
    + constructor.
      * by apply IHHty1.
      * by apply IHHty2.
    + constructor.
      * by apply IHHty1.
      * by apply IHHty2.
      * by apply IHHty3.
    + eapply typed_Throw; try done.
      by apply IHHty.
    + econstructor; first done.
      * apply IHHty1.
        intros [|].
        { term_simpl. apply le_pty_refl. }
        simpl. apply Hag.
      * by apply IHHty2.
   Qed.
   *)
  (*
   Lemma weakening_errors {S} : ∀ Γ τ1 τ2 (e : expr S),
    (Γ ⊢ₑ e : τ1) →
    τ1 ⪍ τ2 →
    (Γ ⊢ₑ e : τ2).
  Proof.
    intros. by eapply typed_wk.
    revert S.
    fix IHHty 7.
    intros S Γ [τ1 E1] [τ2 E2] e Hty Hle.
    inversion Hty; subst.
    - constructor. inversion Hle. subst. by eapply le_pty_trans.
    - inversion Hle. subst. inversion H2. subst. constructor.
    - inversion Hle. subst. inversion H3. subst.
      { done.
      constructor.
      eapply IHHty; last done.
      eapply weakening_sub; first done.
        intros [|[|]].
        { done. }
        { constructor. 

    
    intros Γ [τ1 E1] τ2 e Hty.
    revert τ2.
    induction Hty; intros [τ2 E2] Hτ.
    - inversion Hτ. subst. constructor.
    inversion Hty; subst.
    - by constructor.
    - by constructor.
    - by constructor. 
    - econstructor.
      { inversion H3; subst.
        + constructor.
        
      } (** eapply IHHty; last done. } **)
      { by eapply IHHty. }
    - constructor.
      { by eapply IHHty. }
      { by eapply IHHty. }
    - constructor.
      { by eapply IHHty. }
      { by eapply IHHty. }
      { by eapply IHHty. }
    - econstructor; first done.
      { by apply HE. }
      by eapply IHHty.
    - econstructor; first done.
      { by eapply IHHty. }
      { eapply IHHty; first done. intros x [|]; auto. }
  Qed. 
       *)
  Lemma substitution_lemma {S : Set}:
    ∀ (e : expr S) (E : exc → Prop) T Γ Δ (γ : S [⇒] T) τ, (Γ ⊢ₑ e : τ ⇑ E)
                            → (∀ (x : S), Δ ⊢ₑ γ x : Γ x ⇑ ⋆)
                            → ( Δ  ⊢ₑ bind γ e : τ ⇑ E).
  Proof.
    - revert S.
      intros S e E T Γ Δ γ τ Hty.
      generalize dependent T.
      induction Hty; intros.
      + term_simpl.
        subst.
        eapply weakening_error; first done.
        by constructor.
      + term_simpl. constructor.
      + term_simpl. econstructor; first done.
        * apply IHHty.
          intros [|[|]].
          { constructor. simpl. apply le_pty_refl. }
          { constructor. apply le_pty_refl. }
          term_simpl.
          eapply (weakening (Δ ▹ σ ⟶ τ0)).
          { eapply weakening; done.}
          done.
      + term_simpl.
        econstructor; first done.
        * by apply IHHty1.
        * by apply IHHty2.
      + term_simpl.
        econstructor; first done.
        * by apply IHHty1.
        * by apply IHHty2.
      + term_simpl.
        econstructor; first done.
        * by apply IHHty1.
        * by apply IHHty2.
        * by apply IHHty3.
      + term_simpl.
        econstructor; try done.
        by apply IHHty.
      + term_simpl.
        econstructor; try done.
        * apply IHHty1.
          intros [|].
          { term_simpl. constructor. apply le_pty_refl. }
          { term_simpl. eapply weakening; last done. apply H1. }
        * by apply IHHty2.
  Qed.

  
  Lemma weakening_cont {S T : Set} :
    ∀ (Γ : S → pty) (Δ : T → pty) (δ : S [→] T) (K : cont S) σ τ,
    (Γ ⊢ₖ K : σ ⇒ τ) →
    (Δ • δ ≡ Γ) →
    (Δ ⊢ₖ (fmap δ K) : σ ⇒ τ).
   Proof.
    intros Γ Δ δ e σ τ Hty Hag.
    generalize dependent T.
    induction Hty; intros.
    - term_simpl. by constructor.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      all : by eapply weakening.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      change (Val (fmap δ v)) with (fmap δ (Val v)).
      by eapply weakening.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      all : by eapply weakening.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      change (Val (fmap δ v)) with (fmap δ (Val v)).
      by eapply weakening.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      all : by eapply weakening.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      all : done.
    - term_simpl. econstructor; last by eapply IHHty.
      { eauto. }
      { done. }
      { done. }
      eapply weakening; first done.
      intros [|]; first done.
      apply Hag.
   Qed.
   
   Lemma weakening_error_cont {S : Set} :
     ∀ (Γ : S → pty) (K : cont S) σ1 σ2 τ1 τ2,
    (Γ ⊢ₖ K : σ1 ⇒ τ1) →
     σ2 ⪍ σ1 →
     τ1 ⪍ τ2 →
    (Γ ⊢ₖ K : σ2 ⇒ τ2).
  Proof.
    intros Γ K [σ1 Eσ1] σ2 [τ1 Eτ1] τ2 Hty.
    revert σ2 τ2.
    induction Hty; intros [σ' Eσ'] [ρ Eρ] Hσ Hτ.
    - constructor. eapply le_ty_trans; first done.
      by eapply le_ty_trans.
    - inversion Hσ. subst. inversion H5. subst.
      econstructor; last apply IHHty.
      { intros ? [[|]|]; apply H.
        * left. left. by apply H7.
        * left. right. apply H2.
        * right. apply H2. }
      all : try done.
      constructor; first by apply le_pty_refl.
      eauto.
    - inversion Hσ. subst. inversion H4. subst.
      inversion H7. subst.
      econstructor; last apply IHHty.
      { intros ? [[|]|]; apply H.
        * left. left. by apply H9.
        * left. right. by apply H6.
        * right. apply H1. }
      all : try done.
      by eapply weakening_error.
      
    - inversion Hσ. subst.
      econstructor; last eapply IHHty.
      { intros ? [[|]|]; apply H.
        * left. by left.
        * left. by right.
        * right. eauto.
      }
      all : try done.
      + eapply weakening_error; first done.
        constructor; last by apply le_set_refl.
        constructor; first done.
        apply le_ty_refl.
      + constructor; last by eauto.
        apply le_pty_refl.
    - inversion Hσ. subst.
      inversion H4. subst.
      econstructor; last by apply IHHty.
      { intros ? [|]; apply H.
        * left. apply H1.
        * right. eauto. 
      }
      done.
    - inversion Hσ. subst.
      inversion H4. subst.
      econstructor; last by apply IHHty.
      { intros ? [|]; apply H.
        * left. apply H1.
        * right. eauto. 
      }
      done.
    - inversion Hσ. subst.
      econstructor; first by eapply le_pty_trans.
      { intros ? [|]; apply H0.
        * by left.
        * right. eauto.
      }
      apply IHHty.
      + constructor; first by apply le_pty_refl.
        eauto.
      + done.
    - inversion Hσ. subst.
      inversion Hτ. subst.
      econstructor.
      { done. }
      { by eapply le_pty_trans. }
      { intros ? [|]; apply H1.
        * by left.
        * right. destruct H3. split; eauto.
      }
      { done. }
      apply IHHty; last done.
      constructor; last by apply le_set_refl.
      apply le_pty_refl.
  Qed. 

  Lemma fill_bind_bind {S T}: ∀ (δ : S [⇒] T) K e, fill (bind δ K) (bind δ e) = bind δ (fill K e).
  Proof.
    intros δ K.
    revert δ.
    induction K; first done; 
      term_simpl; intros;
      change (BindCore_expr _ _ δ (fill K ?e) ) with (bind δ (fill K e));
      rewrite -IHK;
      done.
  Qed.
  
  Lemma fill_bind_subst {S}: ∀ (K : cont S) e e', fill K (subst e e') = subst (fill (shift K) e) e'.
  Proof.
    intros K.
    induction K;
     try done;
     term_simpl; intros;
      change (BindCore_expr _ _ (mk_subst ?e') (fill (shift K) ?e) ) with (subst (fill (shift K) e) e');
      rewrite -IHK;
      term_simpl; try done.
    repeat f_equal.
    by rewrite subst_shift_id_lifted.
  Qed.

  Lemma decomp_types {S} : ∀ (K : cont S) e Γ τ, (Γ ⊢ₑ fill K e : τ)
                                                  → ∃ α, (Γ ⊢ₑ e : α) ∧ (Γ ⊢ₖ K : α ⇒ τ).
  Proof.
    intros K.
    induction K;
      intros e' Γ τ Hty.
    - exists τ.
      split; first done.
      constructor.
      apply le_ty_refl.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      by econstructor.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      by econstructor.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      econstructor; last done; done.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      econstructor; last done; last done. intros. apply H3. rewrite or_comm. done.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      econstructor; last done; done.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      by econstructor.
    - simpl in Hty.
      apply IHK in Hty as (α & Hα & HK).
      inversion Hα; subst.
      eexists.
      split; first done.
      econstructor; try done.
      apply le_pty_refl.
  Qed.

  Lemma fill_types {S : Set} :
    ∀ (K : cont S) e Γ σ τ,
    (Γ ⊢ₖ K : σ ⇒ τ ) → 
    (Γ ⊢ₑ e : σ) → 
    (Γ ⊢ₑ fill K e : τ).
  Proof.
    intros K.
    induction K; intros e' Γ σ τ HK He'; inversion HK; subst.
    { term_simpl. by eapply weakening_error. }
    4 : { simpl. eapply IHK; first done. econstructor; last done; last done. intros. apply H3. by apply or_comm. }
    all:  simpl;
    eapply IHK; try done;
      try econstructor; try done.
    by eapply weakening_error.
  Qed.

  Lemma compose_END_left {S} : ∀ (K : cont S), cont_compose END K = K.
  Proof.
    intros K.
    induction K.
    { done. }
    all : simpl; by rewrite IHK.
  Qed.

  Lemma compose_type {S} : ∀ (K K1 K2 : cont S) Γ σ τ,
    (Γ ⊢ₖ K : σ ⇒ τ) →
    K = cont_compose K1 K2 →
    ∃ α, (Γ ⊢ₖ K1 : α ⇒ τ) ∧ (Γ ⊢ₖ K2 : σ ⇒ α).
  Proof.
    intros K K1 K2 Γ σ τ HK.
    revert K1 K2.
    induction HK; intros K1 K2 Heq.
    - destruct K1, K2 ; try discriminate.
      eexists. split; econstructor; try done. apply le_ty_refl.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl. 
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α &  HK1 & HK2).
        eexists. split; first done. by econstructor.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl.
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α0 & HK1 & HK2).
        eexists. split; first done. by econstructor.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl.
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α0 & HK1 & HK2).
        eexists. split; first done. by econstructor.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl.
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α & HK1 & HK2).
        eexists. split; first done. by econstructor.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl.
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α & HK1 & HK2).
        eexists. split; first done. by econstructor.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl.
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α0 & HK1 & HK2).
        eexists. split; first done. by econstructor.
    - destruct K2; try discriminate.
      + simpl in Heq. subst.
        eexists. split; econstructor; try done. apply le_ty_refl.
      + injection Heq. intros. subst.
        destruct (IHHK K1 K2 eq_refl) as (α0 & HK1 & HK2).
        eexists. split; first done. by econstructor.
  Qed.

  Lemma less_errors_catch {S} :
    ∀ (K : cont S) Γ σ τ E1 E2 err,
    (Γ ⊢ₖ K : (σ ⇑ E1) ⇒ (τ ⇑ E2)) →
    E1 err ∧ ¬ E2 err →
    ∃ K1 K2 h, K = cont_compose (CatchK err h K1) K2.
  Proof.
    intros K.
    induction K; intros Γ σ τ E1 E2 err0 Hty [HE1 HE2]; inversion Hty; subst.
    - contradict HE2. inversion H. subst. eauto.
    - apply (IHK _ _ _ _ _ err0) in H9 as (K1 & K2 & h & ->); last eauto.
      by exists K1, (IfK e₁ e₂ K2), h.
    - apply (IHK _ _ _ _ _ err0) in H7 as (K1 & K2 & h & ->); last eauto.
      by exists K1, (AppLK v K2), h.
    - apply (IHK _ _ _ _ _ err0) in H7 as (K1 & K2 & h & ->); last eauto.
      by exists K1, (AppRK e K2), h.
    - apply (IHK _ _ _ _ _ err0) in H8 as (K1 & K2 & h & ->); last eauto.
      by exists K1, (NatOpLK op v K2), h.
    - apply (IHK _ _ _ _ _ err0) in H8 as (K1 & K2 & h & ->); last eauto.
      by exists K1, (NatOpRK op e K2), h.
    - apply (IHK _ _ _ _ _ err0) in H7 as (K1 & K2 & h & ->); last eauto.
      by exists K1, (ThrowK err K2), h.
    - destruct (eq_dec err err0) as [-> | Hdiff].
      + by exists K, END, h.
      + apply (IHK _ _ _ _ _ err0) in H10 as (K1 & K2 & h0 & ->); last eauto.
        by exists K1, (CatchK err h K2), h0.
    Qed.
  
  Lemma preservation {S} :
    ∀ Γ τ1 (c c' : @config S) n,
    (Γ ⊢ᵢ c : τ1) →
    c ===> c' / n → 
    ∃ τ2, τ2 ⪍ τ1 ∧ (Γ ⊢ᵢ c' : τ2).
  Proof.
    intros Γ τ c c' n Hty Hred.
    revert Γ τ Hty.
    induction Hred; intros Γ [τ Eτ] Hty; simpl; eexists; try (split; try done; apply le_ty_refl).
    - simpl in *.
      split; last first.
      + do 2 rewrite fill_bind_subst.
        apply decomp_types in Hty as (α & Hα & HK).
        inversion Hα. subst.
        inversion H3. subst.
        inversion H6. subst.
        eapply (substitution_lemma _ _ _ (Γ ▹ (σ0 ⟶ τ1))).
        * eapply (substitution_lemma _ _ _ (Γ ▹ (σ0 ⟶ τ1) ▹ σ0)).
          -- eapply fill_types. 
             { eapply (weakening_cont (Γ ▹ (σ0 ⟶ τ1))).
             { eapply weakening_cont.
               2 : instantiate (1 := Γ); done.
               apply HK.
             }
             done.
             }
             eapply weakening_error; first by apply H7.
             eapply le_ty_trans; first done.
             constructor; first by apply le_pty_refl.
             eauto.
          -- intros [|[|]]; term_simpl.
             { unfold shift.
               change (Val (fmap ?δ ?v)) with (fmap δ (Val v)). 
               eapply weakening; last by instantiate (1 := Γ).
               inversion H5; subst.
               + inversion H4. constructor.
               + inversion H10. subst. inversion H4. subst. econstructor; last done.
                 constructor; first by eapply le_pty_trans.
                 by eapply le_ty_trans.
             }
             { constructor. apply le_pty_refl. }
             { constructor. apply le_pty_refl. }
        * intros [|]; term_simpl; first econstructor; try done.
          { apply le_pty_refl. }
          constructor. apply le_pty_refl.
      + apply le_ty_refl.
    - apply decomp_types in Hty as [α [Hα HK]].
      inversion HK. subst.
      split; first last.
      + eapply fill_types; first done.
        destruct n; simpl; eapply weakening_error; try done; constructor; try apply le_pty_refl; eauto.
      + apply le_ty_refl.
    - destruct v1, v2; try discriminate.
      simpl in H. injection H as <-.
      apply decomp_types in Hty as [α [Hα HK]].
      inversion HK. subst.
      split; first last.
      + eapply fill_types; first done.
        constructor.
      + apply le_ty_refl.
    - apply decomp_types in Hty as [α [Hα HK]].
      inversion HK. subst.
      split; first last.
      + eapply fill_types; first done.
        inversion Hα; subst.
        { inversion H3. constructor. }
        { econstructor; last done. by eapply le_pty_trans. }
      + apply le_ty_refl.
    - apply decomp_types in Hty as [α [Hα HK]].
      inversion HK. subst.
      apply unwind_decompose in H as (K1 & Hkcomp & HK1).
      destruct (compose_type _ _ _ _ _ _ H7 Hkcomp) as (α & HK2 & HK3).
      inversion HK2. subst.
      split; first last.
      + eapply fill_types; first last.
        * eapply substitution_lemma; first done.
          -- intros [|]; term_simpl.
             { inversion Hα; subst.
               - inversion H2. rewrite -H in H3. inversion H3. subst. constructor.
               - inversion H9. subst. inversion H2. rewrite -H6 in H3. subst.
                 inversion H3. subst.
                 econstructor; last done.
                 constructor.
                 + eapply le_pty_trans; first done.
                   by eapply le_pty_trans.
                 + eapply le_ty_trans; first done.
                   by eapply le_ty_trans.
             }
             constructor.
             apply le_pty_refl.
        * eapply weakening_error_cont; first done.
          { constructor; first by apply le_pty_refl. eauto. }
          eapply le_ty_refl.
      + eapply le_ty_refl.
  Qed.

  Lemma progress : ∀ (c : config) τ, (□ ⊢ᵢ c : τ ⇑ ⋆) → (∃ (v : val ∅), c = Cret v)  ∨ (∃ c' n, c ===> c' / n).
  Proof.
    intros c τ Hty.
    destruct c.
    - right. eexists _, _. constructor.
    - right. destruct c, v; try destruct v0;
      try (apply decomp_types in Hty as (α & H1 & H2);
           inversion H2; subst;
           inversion H1; subst).
      1-3, 5-9,13,17,18 : eexists _, _; by constructor.
      6,7 :  eapply less_errors_catch in H8 as (K1 & K2 & h & HK); eauto;
        apply unwind_decompose_weak in HK as (? & ? & ?);
        eexists _,_;
        by constructor.
      + inversion H7.
      + inversion H8. inversion H6.
      + inversion H6.
      + inversion H6.
      + inversion H6.
    - destruct e; right.
      2 : by inversion Hty.
      all : eexists _,_ ; try constructor.
    - left. eexists. done.
  Qed. 
      
     
    
