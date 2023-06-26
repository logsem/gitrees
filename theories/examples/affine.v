(** Affine functions *)
From Equations Require Import Equations.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang Require Import lang interp.
From gitrees.examples Require Import store pairs.

Module io_lang.
  Definition ty := input_lang.lang.ty.
  Definition expr := input_lang.lang.expr.
  Definition typed {S} := input_lang.lang.typed (S:=S).
  Definition interp_closed {sz} (rs : gReifiers sz) `{!subReifier reify_io rs} (e : expr []) := input_lang.interp.interp_expr rs e ().
End io_lang.

Inductive ty :=
  tBool | tInt | tUnit
| tArr (τ1 τ2 : ty) | tPair (τ1 τ2 : ty).

Inductive expr : scope → Type :=
| LitBool (b : bool) {S} : expr S
| LitNat (n : nat) {S} : expr S
| LitUnit {S} : expr S
| Lam {S} : expr (tt::S) → expr S
| Var {S} : var S → expr S
| App {S1 S2} : expr S1 → expr S2 → expr (S1++S2)
(* | EPair {S} : expr S → expr S → expr S *)
(* | EDestruct {S} : expr S → expr (()::()::S) → expr S *)
| EEmbed {S} : io_lang.expr [] → expr S
.

Local Notation tyctx := (tyctx ty).
Inductive typed : forall {S}, tyctx  S → expr S → ty → Prop :=
| typed_Var {S} (Ω : tyctx S) (τ : ty) (v : var S)  :
  typed_var Ω v τ →
  typed Ω (Var v) τ
| typed_Lam {S} (Ω : tyctx S) (τ1 τ2 : ty) (e : expr (()::S) ) :
  typed (consC τ1 Ω) e τ2 →
  typed Ω (Lam e) (tArr τ1 τ2)
| typed_App {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2) (τ1 τ2 : ty) e1 e2 :
  typed Ω1 e1 (tArr τ1 τ2) →
  typed Ω2 e2 τ1 →
  typed (tyctx_app Ω1 Ω2) (App e1 e2) τ2
| typed_Nat {S} (Ω : tyctx S) n :
  typed Ω (LitNat n) tInt
| typed_Bool {S} (Ω : tyctx S) b :
  typed Ω (LitBool b) tBool
| typed_Unit {S} (Ω : tyctx S) :
  typed Ω LitUnit tUnit
.

Inductive ty_conv : ty → input_lang.lang.ty → Type :=
| ty_conv_bool : ty_conv tBool Tnat
| ty_conv_int  : ty_conv tInt  Tnat
| ty_conv_unit : ty_conv tUnit Tnat
| ty_conv_fun {τ1 τ2 t1 t2} :
  ty_conv τ1 t1 → ty_conv τ2 t2 →
  ty_conv (tArr τ1 τ2) (Tarr (Tarr Tnat t1) t2)
.


Module iolang.
  Context {sz : nat}.
  Variable rs : gReifiers sz.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  Variable s : stuckness.

  Program Definition interp_tnat : ITV -n> iProp := λne αv,
    (∃ n, αv ≡ NatV n)%I.
  Solve All Obligations with solve_proper.
  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp) := λne αv,
    (□ ∀ βv, Φ1 βv -∗ WP@{rs} IT_of_V αv ⊙ (IT_of_V βv) @ s {{ Φ2 }})%I.
  Solve All Obligations with solve_proper.

End iolang.

Definition s : stuckness := λ e, e = OtherError.

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
    LET (t2 env.2) $ λne x,
    LET (t1 env.1) $ λne f,
    APP' f (Thunk x).
  Solve All Obligations with solve_proper_please.
  (* Program Definition interp_destruct {A1 A2 : ofe} *)
  (*      (ps : A1 -n> IT) (t : IT*IT*A2 -n> IT) *)
  (*   : A1*A2 -n> IT := λne env, *)
  (*   LET (ps env.1) $ λne ps, *)
  (*   LET (Thunk (proj1T ps)) $ λne x, *)
  (*   LET (Thunk (proj2T ps)) $ λne y, *)
  (*   t (x, y, env.2). *)
  (* Solve All Obligations with solve_proper_please. *)

  Definition interp_scope_split {S1 S2} {E} :
    interp_scope (E:=E) (S1 ++ S2) -n> interp_scope (E:=E) S1 * interp_scope (E:=E) S2.
  Proof.
    induction S1 as [|? S1]; simpl.
    - simple refine (λne x, (tt, x)).
      solve_proper.
    - simple refine (λne xy, let ss := IHS1 xy.2 in ((xy.1, ss.1), ss.2)).
      solve_proper.
  Defined.

  Fixpoint interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | LitBool b => interp_litbool b
    | LitNat n  => interp_litnat n
    | LitUnit   => interp_litunit
    | Var v     => interp_var v
    | Lam e    => interp_lam (interp_expr e)
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2) ◎ interp_scope_split
    | EEmbed io_expr => constO (io_lang.interp_closed rs io_expr)
    end.

  (* interpreting tys *)
  Program Definition protected (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
    (WP@{rs} Force (IT_of_V αv) @ s {{ Φ }})%I.
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
    (∀ βv, Φ1 βv -∗
             WP@{rs} ((IT_of_V αv) ⊙ (Thunk (IT_of_V βv))) @ s {{ Φ2 }})%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tBool => interp_tbool
    | tUnit => interp_tunit
    | tInt  => interp_tnat
    | tPair τ1 τ2 => interp_tpair (interp_ty τ1) (interp_ty τ2)
    | tArr τ1 τ2  => interp_tarr  (interp_ty τ1) (interp_ty τ2)
    end.

  Definition ssubst_valid {S} (Ω : tyctx S) (ss : ssubst S) : iProp :=
    ([∗ list] τx ∈ zip (list_of_tyctx Ω) (list_of_ssubst (E:=F) ss),
      interp_ty (τx.1) (τx.2))%I.

  Definition valid1 {S} (Ω : tyctx S) (α : interp_scope S -n> IT) (τ : ty) : iProp :=
    ∀ ss, ssubst_valid Ω ss -∗ heap_ctx -∗ WP@{rs} α (interp_ssubst ss) @ s {{ interp_ty τ }}.

  Lemma compat_bool {S} b (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_litbool b) tBool.
  Proof.
    iIntros (αs) "Has #Hctx".
    simpl. iApply wp_val. iModIntro.
    destruct b; simpl; eauto.
  Qed.
  Lemma compat_nat {S} n (Ω : tyctx S) :
    ⊢ valid1 Ω (interp_litnat n) tInt.
  Proof.
    iIntros (αs) "Has #Hctx".
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.
  Lemma compat_unit {S} (Ω : tyctx S) :
    ⊢ valid1 Ω interp_litunit tUnit.
  Proof.
    iIntros (αs) "Has #Hctx".
    simpl. iApply wp_val. iModIntro. eauto.
  Qed.

  (* Lemma compat_pair {A1 A2 : ofe} (e1 : A1) (e2 : A2) (Φ1 Φ2 : ITV -n> iProp) *)
  (*   (α : A1 -n> IT) (β : A2 -n> IT) s : *)
  (*   heap_ctx ⊢ WP@{rs} α e1 @ s {{ Φ1 }} -∗ *)
  (*              WP@{rs} β e2 @ s {{ Φ2 }} -∗ *)
  (*              WP@{rs} interp_pair α β (e1,e2) @ s {{ interp_tpair Φ1 Φ2 }}. *)
  (* Proof. *)
  (*   iIntros "#Hctx H1 H2". *)
  (*   Opaque pairTV. iSimpl. *)
  (*   iApply (wp_bind _ (get_val _)). *)
  (*   { solve_proper. } *)
  (*   iApply (wp_wand with "H2"). *)
  (*   iIntros (βv) "H2". iModIntro. *)
  (*   rewrite get_val_ITV. simpl. *)
  (*   iApply (wp_bind _ (get_val _)). *)
  (*   { solve_proper. } *)
  (*   iApply (wp_wand with "H1"). *)
  (*   iIntros (αv) "H1". iModIntro. *)
  (*   rewrite get_val_ITV. simpl. *)
  (*   iApply wp_val. *)
  (*   iModIntro. *)
  (*   iExists αv,βv. iSplit; eauto with iFrame. *)
  (* Qed. *)
  (* Lemma compat_destruct {A1 A2 : ofe} (e1 : A1) (e2 : A2) *)
  (*   (Φ1 Φ2 Φ : ITV -n> iProp) (α : IT*IT*A2 -n> IT) (β : A1 -n> IT) s : *)
  (*   heap_ctx ⊢ WP@{rs} β e1 @ s {{ interp_tpair Φ1 Φ2 }} -∗ *)
  (*              (∀ β1v β2v, protected Φ1 β1v -∗ protected Φ2 β2v -∗ *)
  (*                     WP@{rs} α (IT_of_V β1v,IT_of_V β2v,e2) @ s {{ Φ }}) -∗ *)
  (*              WP@{rs} (interp_destruct β α (e1,e2)) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   Local Opaque thunked thunkedV proj1T proj2T pairTV. *)
  (*   iIntros "#Hctx H1 H2". *)
  (*   iSimpl. *)
  (*   iApply wp_let. *)
  (*   iApply (wp_wand with "H1"). *)
  (*   iIntros (βv) "H1". iModIntro. *)
  (*   iApply wp_let. *)
  (*   iApply (wp_alloc with "Hctx"). *)
  (*   { solve_proper_please. } *)
  (*   iNext. iNext. iIntros (l1) "Hl1". *)
  (*   iApply (wp_val _ _ (thunkedV _ _)). *)
  (*   iModIntro. iSimpl. *)
  (*   iApply wp_let. *)
  (*   iApply (wp_alloc with "Hctx"). *)
  (*   { solve_proper_please. } *)
  (*   iNext. iNext. iIntros (l2) "Hl2". *)
  (*   iApply (wp_val _ _ (thunkedV _ _)). *)
  (*   iModIntro. iSimpl. *)
  (*   iSimpl in "H1". *)
  (*   iDestruct "H1" as (βv1 βv2) "(#Hb & Hb1 & Hb2)". *)
  (*   iRewrite "Hb". iClear "Hb". *)
  (*   Local Transparent thunkedV thunked. *)
  (*   iApply ("H2" with "[Hb1 Hl1] [Hb2 Hl2]"). *)
  (*   - simpl. iApply wp_lam. iNext. *)
  (*     simpl. *)
  (*     iApply (wp_bind _ (IFSCtx _ _)). *)
  (*     iApply (wp_read with "Hctx Hl1"). *)
  (*     iNext. iNext. iIntros "Hl1". *)
  (*     iApply wp_val. iModIntro. *)
  (*     unfold IFSCtx. simpl. *)
  (*     rewrite IF_False; last lia. *)
  (*     iApply wp_seq. *)
  (*     { solve_proper. } *)
  (*     iApply (wp_write with "Hctx Hl1"). *)
  (*     iNext. iNext. iIntros "Hl1". *)
  (*     rewrite proj1T_pairV. simpl. *)
  (*     repeat (iApply wp_tick; iNext). *)
  (*     by iApply wp_val. *)
  (*   - simpl. iApply wp_lam. iNext. *)
  (*     simpl. *)
  (*     iApply (wp_bind _ (IFSCtx _ _)). *)
  (*     iApply (wp_read with "Hctx Hl2"). *)
  (*     iNext. iNext. iIntros "Hl2". *)
  (*     iApply wp_val. iModIntro. *)
  (*     unfold IFSCtx. simpl. *)
  (*     rewrite IF_False; last lia. *)
  (*     iApply wp_seq. *)
  (*     { solve_proper. } *)
  (*     iApply (wp_write with "Hctx Hl2"). *)
  (*     iNext. iNext. iIntros "Hl2". *)
  (*     rewrite proj2T_pairV. simpl. *)
  (*     repeat (iApply wp_tick; iNext). *)
  (*     by iApply wp_val. *)
  (* Qed. *)

  Lemma compat_var {S} Ω τ (v : var S) :
    typed_var Ω v τ →
    ⊢ valid1 Ω (interp_var v) τ.
  Proof.
    iIntros (Hv ss) "Has #Hctx".
    unfold ssubst_valid.
    iInduction Hv as [|? ? ? Ω v] "IH" forall (ss); simpl.
    - dependent elimination ss as [cons_ssubst αv ss].
      simp list_of_tyctx list_of_ssubst interp_ssubst.
      simp interp_var. simpl.
      iDestruct "Has" as "[H _]".
      by iApply wp_val.
    - dependent elimination ss as [cons_ssubst αv ss].
      simp list_of_tyctx list_of_ssubst interp_ssubst.
      simp interp_var. simpl.
      iDestruct "Has" as "[_ H]".
      iApply ("IH" with "H").
  Qed.

  Lemma compat_app {S1 S2} (Ω1 : tyctx S1) (Ω2 : tyctx S2)
    α β τ1 τ2 :
    ⊢ valid1 Ω1 α (tArr τ1 τ2) -∗
      valid1 Ω2 β τ1 -∗
      valid1 (tyctx_app Ω1 Ω2) (interp_app α β ◎ interp_scope_split) τ2.
  Proof.
    iIntros "H1 H2".
    iIntros (αs) "Has #Hctx".
    iEval(cbn-[interp_app]).
    rewrite ctx_valid_split.
    destruct (interp_ty_ctx_split αs) as [a1 a2].
    iDestruct "Has" as "[Ha1 Ha2]". cbn-[interp_app].
    iSpecialize ("H1" with "Ha1 Hctx").
    iSpecialize ("H2" with "Ha2 Hctx").
    Local Opaque Thunk.
    iSimpl.
    iApply wp_let.
    iApply (wp_wand with "H2").
    iIntros (βv) "H2".
    iModIntro. iSimpl.
    iApply wp_let.
    iApply (wp_wand with "H1").
    iIntros (αv) "H1".
    iModIntro. iSimpl.
    by iApply "H1".
  Qed.

  Lemma compat_lam Ω τ1 τ2 α :
    ⊢ valid1 (τ1::Ω) α τ2 -∗
      valid1 Ω (interp_lam α) (tArr τ1 τ2).
  Proof.
    iIntros "H".
    iIntros (αs) "Has #Hctx".
    iApply wp_val.
    iModIntro. simpl.
    iIntros (βv) "Hb".
    iApply (wp_bind _ (AppRSCtx _)).
    Local Transparent Thunk.
    Local Opaque thunked thunkedV.
    iSimpl. iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext. iIntros (l) "Hl".
    iApply wp_val. iModIntro.
    unfold AppRSCtx.
    iApply wp_lam. iNext.
    iEval(cbn-[thunked]).
    iApply ("H" with "[-] Hctx").
    iSimpl. iFrame "Has".
    iExists _.
    rewrite IT_to_of_V. iSplit; eauto.
    Local Transparent thunked thunkedV.
    iApply wp_lam. iNext. simpl.
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


  Program Definition glue1_fun (glue1 glue2 : IT -n> IT) : IT -n> IT := λne α,
    λit xthnk,
      LET (Force xthnk) $ λne x,
      LET (glue2 x) $ λne x,
      LET (α ⊙ (Thunk x)) glue1.
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
    | ty_conv_fun conv1 conv2 => glue1_fun (glue1 conv1) (glue2 conv2)
    end.

 
  Lemma compat_glue_fun (αv : ITV) (glue1 glue2 : IT -n> IT) (Φ1 Φ2 Φ1' Φ2' : ITV -n> iProp) :
    heap_ctx ⊢
      (∀ βv, Φ1 βv -∗ WP@{rs} glue1 (IT_of_V βv) @ s {{ x, □ Φ1' x }}) -∗
      (∀ βv, Φ2' βv -∗ WP@{rs} glue2 (IT_of_V βv) @ s {{ Φ2 }}) -∗
      (* (unit  →  τ1') → τ2' *)
      □ (∀ βv, □ (WP@{rs} IT_of_V βv ⊙ (Nat 0) @ s {{ Φ1' }}) -∗
             WP@{rs} IT_of_V αv ⊙ (IT_of_V βv) @ s {{ Φ2' }}) -∗
      WP@{rs} glue1_fun glue2 glue1 (IT_of_V αv) @ s {{ interp_tarr Φ1 Φ2 }}.
   Proof.
     iIntros "#Hctx G1 G2 #H1".
     iApply wp_val. iModIntro.
     iIntros (βv) "Hb".
     Local Opaque thunked thunkedV.
     iSimpl. iApply (wp_bind _ (AppRSCtx _)).
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l) "Hl".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iApply wp_lam. iNext.
     iEval(cbn-[thunked]).
     iApply wp_let.
     { solve_proper. }
     iApply wp_lam.
     (* forcing a thunk *)
     iNext. iSimpl.
     iApply (wp_bind _ (IFSCtx _ _)).
     { solve_proper. }
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
     (* doing the glue for the argument *)
     iApply (wp_let).
     { solve_proper. }
     iSpecialize ("G1" with "Hb").
     iApply (wp_wand with "G1").
     iIntros (β'v) "#Hb". iModIntro.
     iSimpl.
     (* calling the original function *)
     iApply wp_let.
     { solve_proper. }
     iApply (wp_bind _ (AppRSCtx _)).
     { solve_proper. }
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l') "Hl'".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iClear "Hl". clear l.
     iApply fupd_wp.
     { solve_proper. }
     iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Nat n)) with "[Hl']") as "#Hinv".
     { iNext. iExists _; done. }
     iSpecialize ("H1" $! (thunkedV (IT_of_V β'v) l') with "[-G2]").
     { iModIntro.
       iApply wp_lam. iNext. iSimpl.
       iApply (wp_bind _ (IFSCtx _ _)).
       iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
       { set_solver. }
       iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
       iModIntro. iExists (Nat n). iFrame.
       iNext. iNext. iIntros "Hl'".
       iMod ("Hcl" with "[Hl']") as "_".
       { iNext. eauto with iFrame. }
       iModIntro. iApply wp_val.
       iModIntro.
       unfold IFSCtx. simpl.
       destruct n as [|n].
       - rewrite IF_False; last lia.
         iApply wp_seq.
         { solve_proper. }
         iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
         { set_solver. }
         iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
         iModIntro. iExists (Nat n). iFrame.
         iNext. iNext. iIntros "Hl'".
         iMod ("Hcl" with "[Hl']") as "_".
         { iNext. eauto with iFrame. }
         iModIntro. iApply wp_val.
         iModIntro. done.
       - rewrite IF_True; last lia.
         iApply wp_err. done. }
     iModIntro.
     iApply (wp_wand with "H1").
     iIntros (γv) "H2".
     iModIntro.
     by iApply "G2".
  Qed.

  Lemma compat_glue2_fun (αv : ITV) (glue1 glue2 : IT -n> IT) (Φ1 Φ2 Φ1' Φ2' : ITV -n> iProp) A :
    heap_ctx ⊢
      □ (∀ βv, Φ1' βv -∗ WP@{rs} glue1 (IT_of_V βv) @ s {{ Φ1 }}) -∗
      □ (∀ βv, Φ2 βv -∗ WP@{rs} glue2 (IT_of_V βv) @ s {{ x, □ Φ2' x }}) -∗
      □ (A -∗ interp_tarr Φ1 Φ2 αv) -∗
      (WP@{rs} glue1_fun glue2 glue1 (IT_of_V αv) @ s {{ αv,
            (* av : (unit →  τ1') → τ2' *)
            □ (∀ βv, □ (WP@{rs} IT_of_V βv ⊙ (Nat 0) @ s {{ Φ1' }}) -∗
                     WP@{rs} IT_of_V αv ⊙ (IT_of_V βv) @ s {{ Φ2' }}) }}).
   Proof.
     iIntros "#Hctx #G1 #G2 #H1 HA".
     iApply wp_val. iModIntro.
     iSpecialize ("H1" with "HA").
     iIntros (βv) "Hb".
     Local Opaque thunked thunkedV.
     iSimpl. iApply (wp_bind _ (AppRSCtx _)).
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l) "Hl".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iApply wp_lam. iNext.
     iEval(cbn-[thunked]).
     iApply wp_let.
     { solve_proper. }
     iApply wp_lam.
     (* forcing a thunk *)
     iNext. iSimpl.
     iApply (wp_bind _ (IFSCtx _ _)).
     { solve_proper. }
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
     (* doing the glue for the argument *)
     iApply (wp_let).
     { solve_proper. }
     iSpecialize ("G1" with "Hb").
     iApply (wp_wand with "G1").
     iIntros (β'v) "#Hb". iModIntro.
     iSimpl.
     (* calling the original function *)
     iApply wp_let.
     { solve_proper. }
     iApply (wp_bind _ (AppRSCtx _)).
     { solve_proper. }
     iApply (wp_alloc with "Hctx").
     { solve_proper. }
     iNext. iNext. iIntros (l') "Hl'".
     iApply wp_val. iModIntro.
     unfold AppRSCtx.
     iClear "Hl". clear l.
     iApply fupd_wp.
     { solve_proper. }
     iMod (inv_alloc (nroot.@"yolo") _ (∃ n, pointsto l' (Nat n)) with "[Hl']") as "#Hinv".
     { iNext. iExists _; done. }
     iSpecialize ("H1" $! (thunkedV (IT_of_V β'v) l') with "[-G2]").
     { iModIntro.
       iApply wp_lam. iNext. iSimpl.
       iApply (wp_bind _ (IFSCtx _ _)).
       iApply (wp_read_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
       { set_solver. }
       iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
       iModIntro. iExists (Nat n). iFrame.
       iNext. iNext. iIntros "Hl'".
       iMod ("Hcl" with "[Hl']") as "_".
       { iNext. eauto with iFrame. }
       iModIntro. iApply wp_val.
       iModIntro.
       unfold IFSCtx. simpl.
       destruct n as [|n].
       - rewrite IF_False; last lia.
         iApply wp_seq.
         { solve_proper. }
         iApply (wp_write_atomic _ _ (⊤∖ nclose (nroot.@"storeE")) with "Hctx").
         { set_solver. }
         iInv (nroot.@"yolo") as (n) "Hl'" "Hcl".
         iModIntro. iExists (Nat n). iFrame.
         iNext. iNext. iIntros "Hl'".
         iMod ("Hcl" with "[Hl']") as "_".
         { iNext. eauto with iFrame. }
         iModIntro. iApply wp_val.
         iModIntro. done.
       - rewrite IF_True; last lia.
         iApply wp_err. done. }
     iModIntro.
     iApply (wp_wand with "H1").
     iIntros (γv) "H2".
     iModIntro.
     by iApply "G2".
   Qed.
