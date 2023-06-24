(** Affine functions *)
From Equations Require Import Equations.
From gitrees Require Import gitree.
From gitrees.examples Require Import store pairs.

Section affine.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_store rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).

  Context `{!invGS Σ, !stateG rs Σ, !heapG rs Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_seq α β Φ `{!NonExpansive Φ} :
    WP@{rs} α {{ _, WP@{rs} β {{ Φ }} }} ⊢ WP@{rs} (SEQ α β) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_bind _ (SEQCtx β)).
    iApply (wp_wand with "H").
    iIntros (?) "Hb". unfold SEQCtx.
    by rewrite SEQ_Val.
  Qed.

  Lemma wp_let α (f : IT -n> IT) Φ `{!NonExpansive Φ} :
    WP@{rs} α {{ αv, WP@{rs} f (IT_of_V αv) {{ Φ }} }} ⊢ WP@{rs} (LET α f) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (wp_bind _ (LETCTX f)).
    iApply (wp_wand with "H").
    iIntros (?) "Hb". simpl.
    by rewrite LET_Val.
  Qed.

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


  Definition scope := (list unit).

  Inductive type :=
     tBool | tInt | tUnit
   | tArr (τ1 τ2 : type) | tPair (τ1 τ2 : type).

  Local Open Scope type.
  Definition interp_litbool (b : bool) {A} : A -n> IT := λne _,
    Nat (if b then 1 else 0).
  Definition interp_litnat (n : nat) {A} : A -n> IT := λne _,
    Nat n.
  Definition interp_litunit {A} : A -n> IT := λne _, Nat 0.
  Program Definition interp_pair {A1 A2} (t1 : A1 -n> IT) (t2 : A2 -n> IT)
    : A1*A2 -n> IT := λne env,
    pairT (t1 env.1) (t2 env.2).
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
    let ps := ps env.1 in
    t (proj1T ps, proj2T ps,env.2).
  Solve All Obligations with solve_proper_please.

  (* interpreting types *)
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
  Program Definition protected (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (WP@{rs} (IT_of_V αv ⊙ (Nat 0)) {{ Φ }})%I.
  Solve All Obligations with solve_proper_please.

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
    rewrite APP'_Fun_l. iEval(cbn-[thunked]).
    rewrite -Tick_eq. iApply wp_tick. iNext.
    iAssert (thunked (IT_of_V βv) l ≡ IT_of_V (thunkedV (IT_of_V βv) l))%I as "Hth".
    { rewrite tv_into_val. done. }
    iRewrite "Hth". iClear "Hth".
    iApply ("H" with "[-]").
    simpl. rewrite APP'_Fun_l/=.
    rewrite -Tick_eq. iApply wp_tick. iNext.
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

  Inductive var : scope → Type :=
  | Vz : forall {S : scope} {s}, var (s::S)
  | Vs : forall {S : scope} {s}, var S -> var (s::S)
  .

  Inductive expr (lang : Type) : scope → Type :=
  | Val {S} : val lang S → expr lang S
  | AffApp {S} : expr lang S → expr lang S → expr lang S
  | EPair {S} : expr lang S → expr lang S → expr lang S
  | EDestruct {S} : expr lang S → expr lang (()::()::S) → expr lang S
  | EEmbed {S} : lang → expr lang S
  with val (lang : Type) : scope → Type :=
  | LitBool (b : bool) {S} : val lang S
  | LitNat (n : nat) {S} : val lang S
  | LitUnit {S} : val lang S
  | VPair {S} : val lang S → val lang S → val lang S
  | VLam {S} : expr lang (()::S) → val lang S
  | Var {S} : var S → val lang S.
