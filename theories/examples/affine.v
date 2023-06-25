(** Affine functions *)
From Equations Require Import Equations.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang Require Import lang interp logrel.
From gitrees.examples Require Import store pairs.

Section affine.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS Σ, !stateG rs Σ, !heapG rs Σ}.
  Notation iProp := (iProp Σ).

  Program Definition thunked : IT -n> locO -n> IT := λne e ℓ,
      λit _, IF (READ ℓ) (Err OtherError)
                         (SEQ (WRITE ℓ (Nat 1)) e).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  Program Definition thunkedV : IT -n> locO -n> ITV := λne e ℓ,
      FunV $ Next (λne _, IF (READ ℓ) (Err OtherError) (SEQ (WRITE ℓ (Nat 1)) e)).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  #[local] Instance tv_into_val e l : IntoVal (thunked e l) (thunkedV e l).
  Proof.
    unfold IntoVal. simpl. f_equiv. f_equiv. intro.
    done.
  Qed.
  Program Definition Thunk : IT -n> IT := λne e,
      ALLOC (Nat 0) (thunked e).
  Solve All Obligations with first [solve_proper|solve_proper_please].
  Program Definition Force : IT -n> IT := λne e, e ⊙ (Nat 0).

  Inductive ty :=
     tBool | tInt | tUnit
   | tArr (τ1 τ2 : ty) | tPair (τ1 τ2 : ty).

  Local Open Scope type.
  Definition interp_litbool (b : bool) {A} : A -n> IT := λne _,
    Nat (if b then 1 else 0).
  Definition interp_litnat (n : nat) {A} : A -n> IT := λne _,
    Nat n.
  Definition interp_litunit {A} : A -n> IT := λne _, Nat 0.
  Program Definition interp_pair {A1 A2} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    pairT (t1 env.1) (t2 env.2).  (* we don't need to evaluate the pair here, i.e. lazy pairs? *)
  Next Obligation. solve_proper_please. Qed.
  Program Definition interp_lam {A : ofe} (b : (IT * A) -n> IT) : A -n> IT := λne env,
    λit x, b (x,env).
  Solve All Obligations with solve_proper_please.
  Program Definition interp_app {A1 A2 : ofe} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    APP' (t1 env.1) (LET (t2 env.2) Thunk).
  Solve All Obligations with solve_proper_please.
  Program Definition interp_destruct {A1 A2 : ofe}
       (ps : A1 -n> IT) (t : IT*IT*A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    LET (ps env.1) $ λne ps,
    LET (Thunk (proj1T ps)) $ λne x,
    LET (Thunk (proj2T ps)) $ λne y,
    t (x, y, env.2).
  Solve All Obligations with solve_proper_please.

  (* interpreting tys *)
  Program Definition protected (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (WP@{rs} Force (IT_of_V αv) {{ Φ }})%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tbool : ITV -n> iProp := λne αv,
    (αv ≡ NatV 0 ∨ αv ≡ NatV 1)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n, αv ≡ NatV n)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tunit : ITV -n> iProp := λne αv,
    (αv ≡ NatV 0)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tpair (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ β1v β2v, IT_of_V αv ≡ pairTV (IT_of_V β1v) (IT_of_V β2v) ∗
                       Φ1 β1v ∗ Φ2 β2v)%I.
  Solve All Obligations with solve_proper_please.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (∃ f, IT_of_V αv ≡ Fun f ∧
        ∀ βv l, Φ1 βv -∗ pointsto l (Nat 0) -∗
             WP@{rs} ((IT_of_V αv) ⊙ (thunked (IT_of_V βv) l)) {{ Φ2 }})%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tBool => interp_tbool
    | tUnit => interp_tunit
    | tInt  => interp_tnat
    | tPair τ1 τ2 => interp_tpair (interp_ty τ1) (interp_ty τ2)
    | tArr τ1 τ2  => interp_tarr  (interp_ty τ1) (interp_ty τ2)
    end.

  Lemma compat_bool b {A :ofe} (e : A) :
    ⊢ WP@{rs} (interp_litbool b e) {{ interp_tbool }}.
  Proof.
    simpl. iApply wp_val. iModIntro.
    destruct b; simpl; eauto.
  Qed.
  Lemma compat_nat n {A :ofe} (e : A) :
    ⊢ WP@{rs} (interp_litnat n e) {{ interp_tnat }}.
  Proof.
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.
  Lemma compat_unit {A :ofe} (e : A) :
    ⊢ WP@{rs} (interp_litunit e) {{ interp_tunit }}.
  Proof.
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.
  Lemma compat_pair {A1 A2 : ofe} (e1 : A1) (e2 : A2) (Φ1 Φ2 : ITV -n> iProp)
    (α : A1 -n> IT) (β : A2 -n> IT) :
    heap_ctx ⊢ WP@{rs} α e1 {{ Φ1 }} -∗
               WP@{rs} β e2 {{ Φ2 }} -∗
               WP@{rs} interp_pair α β (e1,e2) {{ interp_tpair Φ1 Φ2 }}.
  Proof.
    iIntros "#Hctx H1 H2".
    Opaque pairTV. iSimpl.
    iApply (wp_bind _ (get_val _)).
    { solve_proper. }
    iApply (wp_wand with "H2").
    iIntros (βv) "H2". iModIntro.
    rewrite get_val_ITV. simpl.
    iApply (wp_bind _ (get_val _)).
    { solve_proper. }
    iApply (wp_wand with "H1").
    iIntros (αv) "H1". iModIntro.
    rewrite get_val_ITV. simpl.
    iApply wp_val.
    iModIntro.
    iExists αv,βv. iSplit; eauto with iFrame.
  Qed.
  Lemma compat_destruct {A1 A2 : ofe} (e1 : A1) (e2 : A2)
    (Φ1 Φ2 Φ : ITV -n> iProp) (α : IT*IT*A2 -n> IT) (β : A1 -n> IT) :
    heap_ctx ⊢ WP@{rs} β e1 {{ interp_tpair Φ1 Φ2 }} -∗
               (∀ β1v β2v, protected Φ1 β1v -∗ protected Φ2 β2v -∗
                      WP@{rs} α (IT_of_V β1v,IT_of_V β2v,e2) {{ Φ }}) -∗
               WP@{rs} (interp_destruct β α (e1,e2)) {{ Φ }}.
  Proof.
    Local Opaque thunked thunkedV proj1T proj2T pairTV.
    iIntros "#Hctx H1 H2".
    iSimpl.
    iApply wp_let.
    iApply (wp_wand with "H1").
    iIntros (βv) "H1". iModIntro.
    iApply wp_let.
    iApply (wp_alloc with "Hctx").
    { solve_proper_please. }
    iNext. iNext. iIntros (l1) "Hl1".
    iApply (wp_val _ _ (thunkedV _ _)).
    iModIntro. iSimpl.
    iApply wp_let.
    iApply (wp_alloc with "Hctx").
    { solve_proper_please. }
    iNext. iNext. iIntros (l2) "Hl2".
    iApply (wp_val _ _ (thunkedV _ _)).
    iModIntro. iSimpl.
    iSimpl in "H1".
    iDestruct "H1" as (βv1 βv2) "(#Hb & Hb1 & Hb2)".
    iRewrite "Hb". iClear "Hb".
    Local Transparent thunkedV thunked.
    iApply ("H2" with "[Hb1 Hl1] [Hb2 Hl2]").
    - simpl. iApply wp_lam. iNext.
      simpl.
      iApply (wp_bind _ (IFSCtx _ _)).
      iApply (wp_read with "Hctx Hl1").
      iNext. iNext. iIntros "Hl1".
      iApply wp_val. iModIntro.
      unfold IFSCtx. simpl.
      rewrite IF_False; last lia.
      iApply wp_seq.
      { solve_proper. }
      iApply (wp_write with "Hctx Hl1").
      iNext. iNext. iIntros "Hl1".
      rewrite proj1T_pairV. simpl.
      repeat (iApply wp_tick; iNext).
      by iApply wp_val.
    - simpl. iApply wp_lam. iNext.
      simpl.
      iApply (wp_bind _ (IFSCtx _ _)).
      iApply (wp_read with "Hctx Hl2").
      iNext. iNext. iIntros "Hl2".
      iApply wp_val. iModIntro.
      unfold IFSCtx. simpl.
      rewrite IF_False; last lia.
      iApply wp_seq.
      { solve_proper. }
      iApply (wp_write with "Hctx Hl2").
      iNext. iNext. iIntros "Hl2".
      rewrite proj2T_pairV. simpl.
      repeat (iApply wp_tick; iNext).
      by iApply wp_val.
  Qed.
  Lemma compat_app {A1 A2 :ofe} (e1 : A1) (e2 : A2) Φ1 Φ2
    (α : A1 -n> IT) (β : A2 -n> IT) :
    heap_ctx ⊢ WP@{rs} α e1 {{ interp_tarr Φ1 Φ2 }} -∗
               WP@{rs} β e2 {{ Φ1 }} -∗
               WP@{rs} (interp_app α β (e1,e2)) {{ Φ2 }}.
  Proof.
    iIntros "#Hctx H1 H2".
    iSimpl.
    iApply (wp_bind _ (AppRSCtx _)).
    iApply wp_let.
    { solve_proper. }
    iApply (wp_wand with "H2").
    iIntros (βv) "H2".
    iModIntro. iEval(cbn-[thunked]).
    iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext. iIntros (ℓ) "Hl".
    iApply (wp_val _ _ (thunkedV _ _)).
    iModIntro. unfold AppRSCtx.
    iApply (wp_bind _ (AppLSCtx (IT_of_V (thunkedV (IT_of_V βv) ℓ)))).
    { solve_proper. }
    iApply (wp_wand with "H1").
    iIntros (αv) "H1".
    iModIntro. unfold AppLSCtx.
    rewrite tv_into_val.
    iDestruct "H1" as (f) "[Hf H1]".
    iApply ("H1" with "H2 Hl").
  Qed.

  Lemma compat_lam {A : ofe} (e : A) (Φ1 Φ2 : ITV -n> iProp) (α : IT*A -n> IT) :
    heap_ctx ⊢ (∀ βv, protected Φ1 βv -∗ WP@{rs} α (IT_of_V βv,e) {{ Φ2 }}) -∗
               WP@{rs} (interp_lam α e) {{ interp_tarr Φ1 Φ2 }}.
  Proof.
    iIntros "#Hctx H".
    iApply wp_val.
    iModIntro. iExists _; iSplit; eauto.
    iIntros (βv l) "Hb Hl".
    iApply wp_lam. iNext.
    iEval(cbn-[thunked]).
    iAssert (thunked (IT_of_V βv) l ≡ IT_of_V (thunkedV (IT_of_V βv) l))%I as "Hth".
    { rewrite tv_into_val. done. }
    iRewrite "Hth". iClear "Hth".
    iApply ("H" with "[-]").
    simpl. iApply wp_lam. iNext.
    iApply (wp_bind _ (IFSCtx _ _)).
    iApply (wp_read with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    unfold IFSCtx. simpl.
    rewrite IF_False; last lia.
    iApply wp_seq.
    { solve_proper. }
    iApply (wp_write with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    iApply "Hb".
  Qed.

  Inductive expr : scope → Type :=
  | Val {S} : val S → expr S
  | AffApp {S1 S2} : expr S1 → expr S2 → expr (S1++S2)
  (* | EPair {S} : expr S → expr S → expr S *)
  (* | EDestruct {S} : expr S → expr (()::()::S) → expr S *)
  | EEmbed {S} : input_lang.lang.expr S → expr S
  with val : scope → Type :=
  | LitBool (b : bool) {S} : val S
  | LitNat (n : nat) {S} : val S
  | LitUnit {S} : val S
  (* | VPair {S} : val S → val S → val S *)
  | VLam {S} : expr (tt::S) → val S
  | Var {S} : var S → val S.

  Definition split_scope {S1 S2} : interp_scope rs (S1++S2) -n> prodO (interp_scope rs S1) (interp_scope rs S2).
  Proof.
    induction S1 as [|? S1]; simpl.
    - simple refine (λne x, (tt, x)).
      solve_proper.
    - simple refine (λne xy, let ss := IHS1 xy.2 in ((xy.1, ss.1), ss.2)).
      solve_proper.
  Qed.

  Program Definition interp_var {S} (v : var S) : interp_scope rs S -n> IT :=
    λne env, interp_var rs v env ⊙ (Nat 0).
  Solve All Obligations with solve_proper.

  Fixpoint interp_expr {S} (e : expr S) : interp_scope rs S -n> IT :=
    match e with
    | Val v => interp_val v
    | AffApp e1 e2 => interp_app (interp_expr e1) (interp_expr e2) ◎ split_scope
    | EEmbed ei => input_lang.interp.interp_expr rs ei
    end
  with interp_val {S} (v : val S) : interp_scope rs S -n> IT :=
    match v with
    | LitBool b => interp_litbool b
    | LitNat n  => interp_litnat n
    | LitUnit   => interp_litunit
    | Var v     => interp_var v
    | VLam e    => interp_lam (interp_expr e)
    end.

  Inductive ty_conv : ty → input_lang.lang.ty → Type :=
  | ty_conv_bool : ty_conv tBool Tnat
  | ty_conv_int  : ty_conv tInt  Tnat
  | ty_conv_unit : ty_conv tUnit Tnat
  | ty_conv_fun {τ1 τ2 t1 t2} :
    ty_conv τ1 t1 → ty_conv τ2 t2 →
    ty_conv (tArr τ1 τ2) (Tarr (Tarr Tnat t1) t2)
  .

  Program Definition glue1_fun (glue1 glue2 : IT -n> IT) : IT -n> IT := λne α,
    λit x, LET (glue2 (Force x)) $ λne x,
      LET (α ⊙ (Thunk x)) glue1.
  Solve All Obligations with solve_proper_please.
  Program Definition glue2_fun (glue1 glue2 : IT -n> IT) : IT -n> IT := λne α,
    λit x, LET (glue1 (Force x)) $ λne x,
      LET (α ⊙ (Thunk x)) glue2.
  Solve All Obligations with solve_proper_please.

  Program Definition glue2_bool : IT -n> IT := λne α,
      IF α (Nat 1) (Nat 0).

  Fixpoint glue1 {τ t} (conv : ty_conv τ t) : IT -n> IT :=
    match conv with
    | ty_conv_bool => idfun
    | ty_conv_int  => idfun
    | ty_conv_unit => idfun
    | ty_conv_fun conv1 conv2 => glue1_fun (glue1 conv2) (glue2 conv1)
    end
  with glue2  {τ t} (conv : ty_conv τ t) : IT -n> IT :=
    match conv with
    | ty_conv_bool => glue2_bool
    | ty_conv_int  => idfun
    | ty_conv_unit => constO (Nat 0)
    | ty_conv_fun conv1 conv2 => glue2_fun (glue1 conv1) (glue2 conv2)
    end.
