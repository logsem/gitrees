From gitrees Require Export lang_generic gitree program_logic.
From gitrees.examples.input_lang Require Import lang interp.
From gitrees.effects Require Import store.
From gitrees.lib Require Import pairs.

Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

(* for namespace sake *)
Module io_lang.
  Definition state := io_tape.state.
  Definition ty := input_lang.lang.ty.
  Definition expr := input_lang.lang.expr.
  Definition tyctx {S : Set} := S → ty.
  Definition typed {S : Set} := input_lang.lang.typed (S:=S).
  Definition interp_closed {sz} (rs : gReifiers NotCtxDep sz) `{!subReifier reify_io rs} (e : expr ∅) {R} `{!Cofe R, !SubOfe natO R} : IT (gReifiers_ops rs) R :=
    input_lang.interp.interp_expr rs e ı_scope.
End io_lang.

Inductive ty :=
  tBool | tInt | tUnit
| tArr (τ1 τ2 : ty) | tPair (τ1 τ2 : ty)
| tRef (τ : ty).

Inductive ty_conv : ty → io_lang.ty → Type :=
| ty_conv_bool : ty_conv tBool Tnat
| ty_conv_int  : ty_conv tInt  Tnat
| ty_conv_unit : ty_conv tUnit Tnat
| ty_conv_fun {τ1 τ2 t1 t2} :
  ty_conv τ1 t1 → ty_conv τ2 t2 →
  ty_conv (tArr τ1 τ2) (Tarr (Tarr Tnat t1) t2)
.

Inductive expr : ∀ (S : Set), Type :=
| LitBool {S : Set} (b : bool) : expr S
| LitNat {S : Set} (n : nat) : expr S
| LitUnit {S : Set} : expr S
| Lam {S : Set} : expr (inc S) → expr S
| Var {S : Set} : S → expr S
| App {S1 S2 : Set} : expr S1 → expr S2 → expr (sum S1 S2)
| EPair {S1 S2 : Set} : expr S1 → expr S2 → expr (sum S1 S2)
| EDestruct {S1 S2 : Set} : expr S1 → expr (inc (inc S2)) → expr (sum S1 S2)
| Alloc {S : Set} : expr S → expr S
| Replace {S1 S2 : Set} : expr S1 → expr S2 → expr (sum S1 S2)
| Dealloc {S : Set} : expr S → expr S
| EEmbed {S : Set} {τ1 τ1'} : io_lang.expr ∅ → ty_conv τ1 τ1' → expr S
.

Section affine.
  Context {sz : nat}.
  Variable rs : gReifiers NotCtxDep sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R : ofe}.
  Context `{!Cofe R, !SubOfe unitO R, !SubOfe natO R, !SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
  Notation iProp := (iProp Σ).

  Program Definition thunked : IT -n> locO -n> IT := λne e ℓ,
      λit _, IF (READ ℓ) (Err OtherError)
                         (SEQ (WRITE ℓ (Ret 1)) e).
  Solve All Obligations with first [solve_proper|solve_proper_please].

  Program Definition thunkedV : IT -n> locO -n> ITV := λne e ℓ,
      FunV $ Next (λne _, IF (READ ℓ) (Err OtherError) (SEQ (WRITE ℓ (Ret 1)) e)).
  Solve All Obligations with first [solve_proper|solve_proper_please].

  #[export] Instance thunked_into_val e l : IntoVal (thunked e l) (thunkedV e l).
  Proof.
    unfold IntoVal. simpl. f_equiv. f_equiv. intro. done.
  Qed.

  Program Definition Thunk : IT -n> IT := λne e,
      ALLOC (Ret 0) (thunked e).
  Solve All Obligations with first [solve_proper|solve_proper_please].

  Program Definition Force : IT -n> IT := λne e, e ⊙ (Ret 0).

  Local Open Scope type.

  Definition interp_litbool {A} (b : bool)  : A -n> IT := λne _,
      Ret (if b then 1 else 0).

  Definition interp_litnat {A}  (n : nat) : A -n> IT := λne _,
      Ret n.

  Definition interp_litunit {A} : A -n> IT := λne _, Ret tt.

  Program Definition interp_pair {A1 A2} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1 * A2 -n> IT := λne env,
    pairIT (t1 env.1) (t2 env.2).  (* we don't need to evaluate the pair here, i.e. lazy pairs? *)
  Next Obligation. solve_proper_please. Qed.

  Program Definition interp_lam {S : Set} (b : @interp_scope F R _ (inc S) -n> IT) : @interp_scope F R _ S -n> IT := λne env, (λit x, (b (@extend_scope F R _ _ env x))).
  Next Obligation.
    intros; repeat intro; repeat f_equiv; assumption.
  Qed.
  Next Obligation.
    intros; repeat intro; repeat f_equiv; intro; simpl;
      f_equiv; intro z; simpl.
    destruct z; done.
  Qed.

  Program Definition interp_app {A1 A2 : ofe} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    LET (t2 env.2) $ λne x,
    LET (t1 env.1) $ λne f,
    APP' f (Thunk x).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_alloc {A} (α : A -n> IT) : A -n> IT := λne env,
    LET (α env) $ λne α, ALLOC α Ret.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_replace {A1 A2} (α : A1 -n> IT) (β : A2 -n> IT) : A1*A2 -n> IT := λne env,
    LET (β env.2) $ λne β,
    flip get_ret (α env.1) $ λne (l : loc),
    LET (READ l) $ λne γ,
    SEQ (WRITE l β) (pairIT γ (Ret l)).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_dealloc {A} (α : A -n> IT) : A -n> IT := λne env,
    get_ret DEALLOC (α env).
  Solve All Obligations with solve_proper_please.

  Program Definition glue_to_affine_fun (glue_from_affine glue_to_affine : IT -n> IT) : IT -n> IT := λne α,
    LET α $ λne α,
    λit xthnk,
      LET (Force xthnk) $ λne x,
      LET (glue_from_affine x) $ λne x,
      LET (α ⊙ (Thunk x)) glue_to_affine.
  Solve All Obligations with solve_proper_please.

  Program Definition glue_from_affine_fun (glue_from_affine glue_to_affine : IT -n> IT) : IT -n> IT := λne α,
    LET α $ λne α,
    LET (Thunk α) $ λne α,
    λit xthnk,
      LET (Force α) $ λne α,
      LET (Force xthnk) $ λne x,
      LET (glue_to_affine x) $ λne x,
      LET (α ⊙ (Thunk x)) glue_from_affine.
  Solve All Obligations with solve_proper_please.

  Program Definition glue2_bool : IT -n> IT := λne α,
      IF α (Ret 1) (Ret 0).

  Fixpoint glue_to_affine {τ t} (conv : ty_conv τ t) : IT -n> IT :=
    match conv with
    | ty_conv_bool => glue2_bool
    | ty_conv_int  => idfun
    | ty_conv_unit => constO (Ret tt)
    | ty_conv_fun conv1 conv2 => glue_to_affine_fun (glue_from_affine conv1) (glue_to_affine conv2)
    end
  with glue_from_affine  {τ t} (conv : ty_conv τ t) : IT -n> IT :=
    match conv with
    | ty_conv_bool => idfun
    | ty_conv_int  => idfun
    | ty_conv_unit => constO (Ret 0)
    | ty_conv_fun conv1 conv2 => glue_from_affine_fun (glue_from_affine conv2) (glue_to_affine conv1)
    end.

  Program Definition interp_destruct {S1 S2 : Set}
    (ps : @interp_scope F R _ S1 -n> IT)
    (t : (@interp_scope F R _ (inc (inc S2)) -n> IT))
    : (@interp_scope F R _ S1 * @interp_scope F R _ S2) -n> IT
    :=  λne env,
      LET (ps env.1) $ λne z,
      LET (Thunk (projIT1 z)) $ λne x,
      LET (Thunk (projIT2 z)) $ λne y,
      (t (@extend_scope F R _ _ (@extend_scope F R _ _ env.2 y) x)).
  Next Obligation.
    intros; repeat intro; repeat f_equiv; assumption.
  Qed.
  Next Obligation.
    intros; repeat intro; repeat f_equiv; intro; simpl; f_equiv; intro A; simpl.
    destruct A as [| [|]]; [assumption | reflexivity | reflexivity].
  Qed.
  Next Obligation.
    intros; repeat intro; repeat f_equiv; first assumption.
    intro; simpl.
    repeat f_equiv; intro; simpl; repeat f_equiv; intro; simpl.
    repeat f_equiv; assumption.
  Qed.
  Next Obligation.
    intros; repeat intro; repeat f_equiv; first assumption.
    intro; simpl; f_equiv; intro; simpl.
    repeat f_equiv; intro; simpl; repeat f_equiv; intro A; simpl.
    destruct A as [| [|]]; [reflexivity | reflexivity |].
    repeat f_equiv; assumption.
  Qed.

  Fixpoint interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | LitBool b => interp_litbool b
    | LitNat n  => interp_litnat n
    | LitUnit   => interp_litunit
    | Var v     => Force ◎ interp_var v
    | Lam e    => interp_lam (interp_expr e)
    | App e1 e2 =>
        interp_app (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EPair e1 e2 =>
        interp_pair (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EDestruct e1 e2 =>
        interp_destruct (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | Alloc e => interp_alloc (interp_expr e)
    | Dealloc e => interp_dealloc (interp_expr e)
    | Replace e1 e2 =>
        interp_replace (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EEmbed e tconv =>
        constO $ glue_to_affine tconv (io_lang.interp_closed _ e)
    end.

  Lemma wp_Thunk (β:IT) s (Φ:ITV → iProp) `{!NonExpansive Φ} :
    ⊢ heap_ctx rs -∗
      ▷ (∀ l, pointsto l (Ret 0) -∗ Φ (thunkedV β l)) -∗
      WP@{rs} Thunk β @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx H".
    iSimpl. iApply (wp_alloc with "Hctx").
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    iApply ("H" with "Hl").
  Qed.
End affine.

#[global] Opaque Thunk.
Arguments Force {_ _ _ _ _}.
Arguments Thunk {_ _ _ _ _ _ _}.
Arguments thunked {_ _ _ _ _ _}.
Arguments thunkedV {_ _ _ _ _ _ _}.

Arguments interp_litbool {_ _ _ _ _ _}.
Arguments interp_litnat {_ _ _ _ _ _}.
Arguments interp_litunit {_ _ _ _ _ _}.
Arguments interp_lam {_ _ _ _ _}.
Arguments interp_app {_ _ _ _ _ _ _ _ _}.
Arguments interp_pair {_ _ _ _ _ _}.
Arguments interp_destruct {_ _ _ _ _ _ _ _ _}.
Arguments interp_alloc {_ _ _ _ _ _ _}.
Arguments interp_dealloc {_ _ _ _ _ _ _ _}.
Arguments interp_replace {_ _ _ _ _ _ _ _ _}.
