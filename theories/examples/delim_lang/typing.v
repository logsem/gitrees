From gitrees.examples.delim_lang Require Import lang.

Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope syn.

Inductive ty :=
| Tnat : ty
| Tarr : ty -> ty -> ty -> ty -> ty
| Tcont : ty → ty → ty.

Declare Scope types.

Notation "'ℕ'" := (Tnat) : types.
Notation "τ '∕' α '→' σ '∕' β" :=
  (Tarr τ α σ β)
    (at level 15
      , σ, α, β at level 10
      , no associativity) : types.
Notation "τ '⤑' σ" := (Tcont τ σ) (at level 10, left associativity) : types.

Reserved Notation "Γ ';' α '⊢ₑ' e ':' τ ';' β"
  (at level 70
    , e at level 60
    , τ, α, β at level 20
    , no associativity).

Reserved Notation "Γ ';' α '⊢ᵥ' e ':' τ ';' β"
  (at level 70
    , e at level 60
    , τ, α, β at level 20
    , no associativity).

Open Scope types.

Inductive typed_expr {S : Set} (Γ : S -> ty) : ty -> expr S -> ty -> ty -> Prop :=
| typed_Val v α τ β :
  (Γ; α ⊢ᵥ v : τ; β) →
  (Γ; α ⊢ₑ v : τ; β)
| typed_Var x τ α :
  (Γ x = τ) →
  (Γ; α ⊢ₑ (Var x) : τ; α)
| typed_App e₁ e₂ γ α β δ σ τ :
  (Γ; γ ⊢ₑ e₁ : σ ∕ α → τ ∕ β; δ) →
  (Γ; β ⊢ₑ e₂ : σ; γ) →
  (Γ; α ⊢ₑ e₁ ⋆ e₂ : τ; δ)
| typed_AppCont e₁ e₂ α β δ σ τ :
  (Γ; σ ⊢ₑ e₁ : τ ⤑ α; δ) →
  (Γ; δ ⊢ₑ e₂ : τ; β) →
  (Γ; σ ⊢ₑ e₁ @k e₂ : α; β)
| typed_NatOp o e₁ e₂ α β γ :
  (Γ; α ⊢ₑ e₁ : ℕ; β) →
  (Γ; β ⊢ₑ e₂ : ℕ; γ) →
  (Γ; α ⊢ₑ NatOp o e₁ e₂ : ℕ; γ)
| typed_If e e₁ e₂ α β σ τ :
  (Γ; β ⊢ₑ e : ℕ; α) →
  (Γ; σ ⊢ₑ e₁ : τ; β) →
  (Γ; σ ⊢ₑ e₂ : τ; β) →
  (Γ; σ ⊢ₑ (if e then e₁ else e₂) : τ; α)
| typed_Shift (e : @expr (inc S)) τ α σ β :
  (Γ ▹ τ ⤑ α; σ ⊢ₑ e : σ; β) →
  (Γ; α ⊢ₑ shift/cc e : τ; β)
| typed_Reset e α σ τ :
  (Γ; σ ⊢ₑ e : σ; τ) →
  (Γ; α ⊢ₑ reset e : τ; α)
where "Γ ';' α '⊢ₑ' e ':' τ ';' β" := (typed_expr Γ α e τ β) : types
with typed_val {S : Set} (Γ : S -> ty) : ty -> val S -> ty -> ty -> Prop :=
| typed_LitV n α :
  (Γ; α ⊢ᵥ #n : ℕ; α)
| typed_RecV (e : expr (inc (inc S))) (δ σ τ α β : ty) :
  (Γ ▹ (σ ∕ α → τ ∕ β) ▹ σ; α ⊢ₑ e : τ; β) ->
  (Γ; δ ⊢ᵥ rec e : σ ∕ α → τ ∕ β; δ)
where "Γ ';' α '⊢ᵥ' e ':' τ ';' β" := (typed_val Γ α e τ β) : types
.

Module Example.
  Open Scope types.

  Lemma typ_example1 α :
    □; α ⊢ₑ ((#1) + (reset ((#3) + (shift/cc ((($0) @k #5) + (($0) @k #6)))))) : Tnat; α.
  Proof.
    econstructor.
    - do 2 constructor.
    - do 2 econstructor.
      + do 2 constructor.
      + do 2 econstructor.
        * econstructor.
          -- by constructor.
          -- do 2 constructor.
        * econstructor.
          -- by constructor.
          -- do 2 constructor.
  Qed.

End Example.
