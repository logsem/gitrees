From gitrees Require Export prelude gitree lang_generic hom.
From stdpp Require Import gmap.
From gitrees.effects Require Import delim store.
From gitrees.examples.delim_lang Require Import lang interp typing hom.
From iris.algebra Require Import list gmap.
From iris.proofmode Require Import base classes tactics environments.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Import locations.
Require Import Binding.Resolver Binding.Lib Binding.Set Binding.Auto Binding.Env.

From gitrees.examples.delim_lang Require example logpred.

Module embed_lang.

  Definition ty := typing.ty.
  Definition expr := lang.expr.
  Definition tyctx {S : Set} := S → ty.
  Definition typed_expr {S : Set} := typing.typed_expr (S := S).
  Definition typed_val {S : Set} := typing.typed_val (S := S).
  Definition typed_expr_pure {S : Set} := typing.typed_pure_expr (S := S).
  Definition typed_val_pure {S : Set} := typing.typed_pure_val (S := S).
  Definition interp_closed {sz} (rs : gReifiers CtxDep sz)
    `{!subReifier reify_delim rs}
    (e : expr ∅) {R}
    `{!Cofe R, !SubOfe natO R} : IT (gReifiers_ops rs) R :=
    interp.interp_expr rs e ı_scope.

End embed_lang.

Section syntax.

  Definition loc : Set := locations.loc.
  Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

  Inductive expr {X : Set} :=
  | Var (x : X) : expr
  | App (e₁ : expr) (e₂ : expr) : expr
  | LamV (e : @expr (inc X))
  | NatOp (op : nat_op) (e₁ : expr) (e₂ : expr) : expr
  | Alloc (e : expr) : expr
  | Assign (e₁ e₂ : expr) : expr
  | Deref (e : expr) : expr
  | LocV (l : loc)
  | UnitV
  | LitV (n : nat)
  | Embed : embed_lang.expr ∅ → expr.

End syntax.

Arguments expr X%bind : clear implicits.

Section typing.

  Inductive ty :=
  | tNat
  | tUnit
  | tArr (τ1 τ2 : ty)
  | tRef (τ : ty).

  Inductive typed_glued
    : forall {S : Set}, (S → ty) → expr S → ty → Type :=
| typed_GlueNat {S : Set} (Ω : S → ty) e :
  (embed_lang.typed_expr_pure □ e ℕ) →
  typed_glued Ω (Embed e) tNat
| typed_VarG {S : Set} (Ω : S → ty) (v : S) :
  typed_glued Ω (Var v) (Ω v)
| typed_AppG {S : Set} (Ω : S → ty) (τ1 τ2 : ty) e1 e2 :
  typed_glued Ω e1 (tArr τ1 τ2) →
  typed_glued Ω e2 τ1 →
  typed_glued Ω (App e1 e2) τ2
| typed_AllocG {S : Set} (Ω : S → ty) τ e :
  typed_glued Ω e τ →
  typed_glued Ω (Alloc e) (tRef τ)
| typed_AssignG {S : Set} (Ω : S → ty) (τ : ty) e1 e2 :
  typed_glued Ω e1 (tRef τ) →
  typed_glued Ω e2 τ →
  typed_glued Ω (Assign e1 e2) tUnit
| typed_DerefG {S : Set} (Ω : S → ty) (τ : ty) e :
  typed_glued Ω e (tRef τ) →
  typed_glued Ω (Deref e) τ
| typed_NatG {S : Set} (Ω : S → ty) n :
  typed_glued Ω (LitV n) tNat
| typed_UnitG {S : Set} (Ω : S → ty) :
  typed_glued Ω UnitV tUnit
| typed_LamG {S : Set} (Ω : S → ty) (τ1 τ2 : ty) (e : expr (inc S)) :
  typed_glued (Ω ▹ τ1) e τ2 →
  typed_glued Ω (LamV e) (tArr τ1 τ2)
| typed_NatOpG {S : Set} (Ω : S → ty) e1 e2 op :
  typed_glued Ω e1 tNat →
  typed_glued Ω e2 tNat →
  typed_glued Ω (NatOp op e1 e2) tNat.

End typing.

Section interp.

  Context {sz : nat}.
  Variable rs : gReifiers CtxDep sz.
  Context `{!subReifier reify_delim rs}.
  Context `{!subReifier (sReifier_NotCtxDep_min reify_store CtxDep) rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
  Notation iProp := (iProp Σ).

  Definition interp_nat {A} (n : nat) : A -n> IT := λne _,
      Ret n.

  Definition interp_unit {A} : A -n> IT := λne _, Ret tt.

  Definition interp_loc {A} (l : loc) : A -n> IT := λne _,
      Ret l.

  Program Definition interp_lam {S : Set} (b : interp_scope (inc S) -n> IT)
    : interp_scope S -n> IT := λne env, (λit x, (b (extend_scope env x))).
  Next Obligation.
    intros; repeat intro; repeat f_equiv; assumption.
  Qed.
  Next Obligation.
    intros; repeat intro; repeat f_equiv; intro; simpl;
      f_equiv; intro z; simpl.
    destruct z; done.
  Qed.

  Program Definition interp_app {A : ofe} (t1 : A -n> IT) (t2 : A -n> IT)
    : A -n> IT := λne env,
      LET (t2 env) $ λne x,
      LET (t1 env) $ λne f,
      APP' f x.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_alloc {A} (α : A -n> IT) : A -n> IT := λne env,
      LET (α env) $ λne α, ALLOC α Ret.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_deref {A} (α : A -n> IT) : A -n> IT := λne env,
      flip get_ret (α env) $ λne (l : loc), READ l.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_assign {A} (α : A -n> IT) (β : A -n> IT) : A -n> IT :=
    λne env,
      LET (β env) $ λne β,
      flip get_ret (α env) $ λne (l : loc),
      (WRITE l β).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Program Fixpoint interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | Var x => interp_var x
    | App n m => interp_app (interp_expr n) (interp_expr m)
    | LamV e => interp_lam (interp_expr e)
    | NatOp op n m => interp_natop op (interp_expr n) (interp_expr m)
    | Alloc e => interp_alloc (interp_expr e)
    | Assign n m => interp_assign (interp_expr n) (interp_expr m)
    | Deref e => interp_deref (interp_expr e)
    | LocV l => interp_loc l
    | UnitV => interp_unit
    | LitV n => interp_nat n
    | Embed e => constO $ (RESET ◎ NextO) (embed_lang.interp_closed  _ e)
    end.

  (* Section example. *)

  (*   Definition test_pr1 : expr ∅ *)
  (*     := App (LamV (Alloc (Var VZ))) *)
  (*          (Embed (reset (gitrees.examples.delim_lang.example.p))). *)

  (*   Lemma p_typ : embed_lang.typed_expr_pure □ (reset (example.p)) ℕ. *)
  (*   Proof. *)
  (*     repeat econstructor. *)
  (*   Qed. *)

  (*   Lemma test_typ1 : *)
  (*     typed_glued □ test_pr1 (tRef tNat). *)
  (*   Proof. *)
  (*     repeat econstructor. *)
  (*     constructor. *)
  (*   Qed. *)

  (*   Lemma test_helper_prop1 : *)
  (*     ⊢ ∀ x σ (Φ : ITV → iProp), has_substate (laterO_map x :: σ : delim.stateF ♯ IT) *)
  (*       -∗ (∀ v, v ≡ RetV 18 -∗ has_substate (σ : delim.stateF ♯ IT) -∗ WP@{rs} (x (IT_of_V v)) {{ Φ }}) *)
  (*       -∗ WP@{rs} 𝒫 (delim_lang.interp.interp_expr rs example.p ı_scope) {{ Φ }}. *)
  (*   Proof. *)
  (*     Opaque SHIFT APP_CONT. *)
  (*     iIntros (x σ Φ) "Hσ HΦ". *)
  (*     cbn. *)
  (*     do 2 example.shift_hom. *)
  (*     iApply (wp_reset with "Hσ"). *)
  (*     iIntros "!> _ Hσ". simpl. *)
  (*     do 2 example.shift_hom. *)
  (*     iApply (wp_shift with "Hσ"). *)
  (*     { rewrite laterO_map_Next. done. } *)
  (*     iIntros "!>_ Hσ". *)
  (*     simpl. *)

  (*     (* the rest *) *)
  (*     rewrite -(IT_of_V_Ret 6) get_val_ITV'. simpl. *)
  (*     rewrite get_fun_fun. simpl. *)
  (*     do 2 example.shift_hom. *)
  (*     iApply (wp_app_cont with "Hσ"); first done. *)
  (*     iIntros "!> _ Hσ". simpl. *)
  (*     rewrite later_map_Next -Tick_eq. *)
  (*     iApply wp_tick. iNext. *)
  (*     example.shift_hom. *)
  (*     rewrite IT_of_V_Ret NATOP_Ret. simpl. *)
  (*     rewrite -(IT_of_V_Ret 9). *)
  (*     iApply (wp_pop_cons with "Hσ"). *)
  (*     iIntros "!> _ Hσ". *)
  (*     simpl. *)

  (*     example.shift_hom. example.shift_natop_l. *)
  (*     rewrite -(IT_of_V_Ret 5) get_val_ITV'. simpl. *)
  (*     example.shift_hom. example.shift_natop_l. *)
  (*     rewrite get_fun_fun. simpl. *)
  (*     example.shift_hom. example.shift_natop_l. *)
  (*     iApply (wp_app_cont with "Hσ"); first done. *)
  (*     iIntros "!> _ Hσ". simpl. *)
  (*     rewrite later_map_Next -Tick_eq. *)
  (*     iApply wp_tick. iNext. *)
  (*     rewrite (IT_of_V_Ret 5) NATOP_Ret. simpl. *)
  (*     rewrite -(IT_of_V_Ret 8). *)
  (*     iApply (wp_pop_cons with "Hσ"). *)
  (*     iIntros "!> _ Hσ". *)
  (*     simpl. *)
  (*     example.shift_hom. *)
  (*     example.shift_natop_l. *)
  (*     rewrite (IT_of_V_Ret 8). *)
  (*     simpl. rewrite IT_of_V_Ret NATOP_Ret. *)
  (*     simpl. rewrite -(IT_of_V_Ret 17). *)
  (*     iApply (wp_pop_cons with "Hσ"). *)
  (*     iIntros "!> _ Hσ". simpl. *)
  (*     rewrite IT_of_V_Ret NATOP_Ret. *)
  (*     simpl. rewrite -(IT_of_V_Ret 18). *)

  (*     iApply (wp_pop_cons with "Hσ"). *)
  (*     iIntros "!> _ Hσ". *)
  (*     by iApply "HΦ". *)
  (*   Qed. *)

  (*   Lemma test_prop1 σ : *)
  (*     ⊢ heap_ctx rs *)
  (*       -∗ has_substate (σ : delim.stateF ♯ IT) *)
  (*       -∗ WP@{rs} (interp_expr test_pr1 ı_scope) @ notStuck *)
  (*            {{ βv, ∃ (l : loc), *)
  (*                     βv ≡ RetV l *)
  (*                     ∗ pointsto l (Ret 18) *)
  (*                     ∗ has_substate (σ : delim.stateF ♯ IT)}}. *)
  (*   Proof. *)
  (*     Opaque SHIFT APP_CONT RESET gitrees.examples.delim_lang.example.p. *)
  (*     iIntros "T H". *)
  (*     cbn. *)

  (*     match goal with *)
  (*     | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] => *)
  (*         set (F := b) *)
  (*     end. *)
  (*     unshelve eset (K := (exist _ (LETCTX F) _ : HOM)). *)
  (*     { apply _. } *)
  (*     Transparent LET. *)
  (*     simpl. *)
  (*     do 2 example.shift_hom. *)
  (*     iApply (wp_reset with "H"). *)
  (*     iNext. *)
  (*     iIntros "? H". *)
  (*     iApply (test_helper_prop1 $! _ σ with "H"). *)
  (*     iIntros (v) "#HEQ H". *)
  (*     subst F. *)
  (*     simpl. *)
  (*     rewrite get_val_ITV. *)
  (*     simpl. *)
  (*     rewrite get_val_fun. *)
  (*     simpl. *)
  (*     rewrite APP'_Fun_l. *)
  (*     simpl. *)
  (*     rewrite <-Tick_eq. *)
  (*     iApply wp_tick. *)
  (*     iNext. *)
  (*     rewrite get_val_ITV. *)
  (*     simpl. *)
  (*     iApply (wp_alloc with "T"). *)
  (*     { solve_proper. } *)
  (*     do 2 iNext. *)
  (*     iIntros (l) "Hl". *)
  (*     iApply wp_val. *)
  (*     iModIntro. *)
  (*     iExists l. *)
  (*     iSplit; first done. *)
  (*     iFrame "H". *)
  (*     assert (Ret 18 ≡ IT_of_V (RetV 18))%stdpp as ->. *)
  (*     { by rewrite -(IT_of_V_Ret 18). } *)
  (*     iRewrite - "HEQ". *)
  (*     done. *)
  (*   Qed. *)
  (* End example. *)
End interp.

Section sets.

  Context {sz : nat}.
  Variable rs : gReifiers CtxDep sz.
  Context `{!subReifier reify_delim rs}.
  Context `{!subReifier (sReifier_NotCtxDep_min reify_store CtxDep) rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} {CR : Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
  Notation iProp := (iProp Σ).

  Canonical Structure exprO S := leibnizO (expr S).

  Notation "'WP' α {{ β , Φ } }" := (wp rs α notStuck ⊤ (λ β, Φ))
                                      (at level 20, α, Φ at level 200,
                                        format "'WP'  α  {{  β ,  Φ  } }") : bi_scope.
  Notation "'WP' α {{ Φ } }" := (wp rs α notStuck ⊤ Φ)
                                  (at level 20, α, Φ at level 200,
                                    format "'WP'  α  {{  Φ  } }") : bi_scope.

  Program Definition clwp : IT -> (ITV -n> iProp) -> iProp :=
    λ α Φ, (∀ (κ : HOM) (Ψ : ITV -n> iProp), (∀ v, Φ v -∗ WP (`κ (IT_of_V v)) {{ Ψ }}) -∗ WP (`κ α) {{ Ψ }})%I.

  Global Instance clwp_ne : NonExpansive2 clwp.
  Proof.
    solve_proper.
  Qed.

  Notation "'CLWP' α {{ β , Φ } }" := (clwp α (λne β, Φ))
                                        (at level 20, α, Φ at level 200,
                                          format "'CLWP'  α  {{  β ,  Φ  } }") : bi_scope.
  Notation "'CLWP' α {{ Φ } }" := (clwp α Φ)
                                    (at level 20, α, Φ at level 200,
                                      format "'CLWP'  α  {{  Φ  } }") : bi_scope.

  Local Instance clwp_bind_ne (κ : HOM) (Φ : ITV -n> iProp)
    : NonExpansive (λ βv, (CLWP (`κ (IT_of_V βv)) {{ Φ }})%I).
  Proof.
    solve_proper.
  Qed.

  Program Definition clwp_bind (κ : HOM) e (Φ : ITV -n> iProp) :
    CLWP e {{ βv, CLWP (`κ (IT_of_V βv)) {{ Φ }} }} ⊢ CLWP (`κ e) {{ Φ }}.
  Proof.
    iIntros "H %κ' %Ψ G".
    rewrite HOM_ccompose.
    iApply ("H" $! (HOM_compose κ' κ)).
    iIntros (v) "J".
    simpl.
    iApply "J".
    iIntros (v') "K".
    by iApply "G".
  Qed.

  Program Definition interp_tnat : ITV -n> iProp := λne αv,
      (∃ n : nat, αv ≡ RetV n)%I.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_tunit : ITV -n> iProp := λne αv,
      (αv ≡ RetV ())%I.
  Solve All Obligations with solve_proper_please.

  Definition logN : namespace := nroot .@ "logN".

  Program Definition interp_ref (Φ : ITV -n> iProp) : ITV -n> iProp := λne αv,
      (∃ (l : loc), αv ≡ RetV l ∗ inv (logN .@ l) (∃ βv, pointsto l (IT_of_V βv) ∗ Φ βv))%I.
  Solve All Obligations with solve_proper_please.

  Program Definition obs_ref : (ITV -n> iProp) -n> IT -n> iProp :=
    λne Ψ α,
       (CLWP α {{ βv, Ψ βv }})%I.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    unfold clwp.
    f_equiv; intro; simpl.
    f_equiv; intro; simpl.
    f_equiv.
    by do 2 f_equiv.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.

  Definition logrel_ectx (V W : ITV -n> iProp) (κ : HOM) : iProp :=
    (□ ∀ (βv : ITV),
       V βv -∗ has_substate ([] : delim.stateF ♯ IT) -∗ obs_ref W (`κ (IT_of_V βv)))%I.

  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp)
    : ITV -n> iProp :=
    λne αv,
      (∃ f', IT_of_V αv ≡ Fun f'
             ∧ □ ∀ βv, Φ1 βv
                       -∗ ∀ κ Φ3, logrel_ectx Φ2 Φ3 κ
                                  -∗ has_substate ([] : delim.stateF ♯ IT)
                                  -∗ obs_ref Φ3 (`κ ((Fun f') ⊙ ((IT_of_V βv)))))%I.
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_ty (τ : ty) : ITV -n> iProp :=
    match τ with
    | tUnit => interp_tunit
    | tNat  => interp_tnat
    | tArr τ1 τ2 => interp_tarr (interp_ty τ1) (interp_ty τ2)
    | tRef τ => interp_ref (interp_ty τ)
    end.

  Global Instance interp_ty_persistent (τ : ty) α :
    Persistent (interp_ty τ α).
  Proof.
    revert α. induction τ=> α; simpl.
    - apply _.
    - apply _.
    - apply _.
    - apply _.
  Qed.

  Program Definition interp_exprG V : IT -n> iProp :=
    λne e, (∀ κ W, heap_ctx rs
                   -∗ has_substate ([] : delim.stateF ♯ IT)
                   -∗ logrel_ectx V W κ
                   -∗ obs_ref W (`κ e))%I.
  Next Obligation.
    solve_proper_prepare.
    f_equiv; intro; simpl.
    f_equiv; intro; simpl.
    do 3 f_equiv.
    unfold clwp.
    f_equiv; intro; simpl.
    f_equiv; intro; simpl.
    f_equiv.
    solve_proper.
  Qed.

  Program Definition ssubst_validG {S : Set}
    (Γ : S -> ty)
    (ss : interp_scope S) : iProp :=
    (∀ x, □ interp_exprG (interp_ty (Γ x)) (ss x))%I.

  Program Definition validG {S : Set}
    (Γ : S -> ty)
    (α : interp_scope S -n> IT)
    (τ : ty) : iProp :=
    (□ ∀ (ss : interp_scope S),
       ssubst_validG Γ ss → interp_exprG (interp_ty τ) (α ss))%I.

  Lemma compat_nat {S : Set} n (Ω : S → ty) :
    ⊢ validG Ω (interp_nat rs n) tNat.
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    iIntros (κ W) "#Q R #W".
    iSpecialize ("W" $! (RetV n) with "[]").
    - iExists _.
      done.
    - by iApply "W".
  Qed.

  Lemma compat_unit {S : Set} (Ω : S → ty) :
    ⊢ validG Ω (interp_unit rs) tUnit.
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    iIntros (κ W) "#Q R #W".
    iSpecialize ("W" $! (RetV ()) with "[]").
    - done.
    - by iApply "W".
  Qed.

  Lemma compat_var {S : Set} (Ω : S → ty) (v : S) :
    ⊢ validG Ω (interp_var v) (Ω v).
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    iIntros (κ W) "Q R W".
    iApply ("H" with "Q R W").
  Qed.

  Lemma compat_glueNat {S : Set} (Ω : S → ty)
    (e : lang.expr ∅)
    (t : embed_lang.typed_expr_pure □ e ℕ)
    : ⊢ validG Ω (interp_expr rs (Embed e)) tNat.
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    iIntros (κ W) "#Q R #W".

    iPoseProof (logpred.fundamental_expr_pure rs □ ℕ e t) as "#G".
    unshelve iSpecialize ("G" $! ı_scope _).
    { iIntros ([]). }
    iIntros "%K %Ψ HH".
    rewrite HOM_ccompose.
    iApply (wp_reset with "R").
    iIntros "!> Hc R".
    iSpecialize ("G" $! (logpred.logrel_nat rs) HOM_id with "[]").
    {
      iApply logpred.compat_HOM_id.
    }
    iSpecialize ("G" $! [laterO_map (`K ◎ `κ)] Ψ with "[HH] R").
    {
      iIntros (v) "#E R".
      iApply (wp_pop_cons with "R").
      iIntros "!> Hc R".
      iSpecialize ("W" with "E R").
      iSpecialize ("W" $! K Ψ with "HH").
      iApply "W".
    }
    iApply "G".
  Qed.

  Lemma compat_app {S : Set}
    (Ω : S → ty)
    α β τ1 τ2 :
    ⊢ validG Ω α (tArr τ1 τ2)
      -∗ validG Ω β τ1
      -∗ validG Ω (interp_app _ α β) τ2.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ W) "#Q R #W".
    simpl.
    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] =>
        set (F := b)
    end.
    unshelve eset (K := (exist _ (LETCTX F) _ : HOM)).
    { apply _. }
    unfold clwp.
    iIntros (Tκ TΨ) "TH".
    assert ((LET (β γ) F) ≡ `K (β γ))%stdpp as ->.
    { reflexivity. }
    rewrite HOM_ccompose.
    iSpecialize ("G" $! γ with "Hγ").
    iSpecialize ("G" $! (HOM_compose κ K)).
    iApply ("G" with "Q R []"); first last.
    { iApply "TH". }
    iClear "G".
    iIntros (v).
    iModIntro.
    iIntros "#T R".
    simpl.
    unfold clwp.
    iIntros (Tκ' TΨ') "TH'".
    rewrite LET_Val.
    subst F K.
    simpl.
    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] =>
        set (F := b)
    end.
    unshelve eset (K := (exist _ (LETCTX F) _ : HOM)).
    { apply _. }
    assert ((LET (α γ) F) ≡ `K (α γ))%stdpp as ->.
    { reflexivity. }
    rewrite HOM_ccompose.
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! (HOM_compose κ K)).
    iApply ("H" with "Q R"); first last.
    { iApply "TH'". }
    iIntros (w).
    iModIntro.
    iIntros "#Hw R".
    simpl.
    unfold clwp.
    iIntros (Tκ'' TΨ'') "TH''".
    rewrite LET_Val.
    subst F.
    simpl.
    iDestruct "Hw" as "(%f & #HEQ & #Hw)".
    iAssert ((IT_of_V w ⊙ (IT_of_V v)) ≡ (Fun f ⊙ (IT_of_V v)))%I as "HEQ'".
    {
      iApply (f_equivI (flipO APP' (IT_of_V v))).
      iApply "HEQ".
    }
    iRewrite "HEQ'".
    iSpecialize ("Hw" $! v with "T").
    iApply ("Hw" $! κ W with "W R").
    iApply "TH''".
  Qed.

  Lemma compat_alloc {S : Set}
    (Ω : S → ty)
    (τ : ty)
    (e : expr S) :
    ⊢ validG Ω (interp_expr rs e) τ -∗ validG Ω (interp_expr rs (Alloc e)) (tRef τ).
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ σ) "#Q R #W".
    simpl.
    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] =>
        set (F := b)
    end.
    unshelve eset (K := HOM_compose κ (exist _ (LETCTX F) _ : HOM)).
    { apply _. }
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! K σ with "Q R []"); first last.
    { subst K; simpl; iApply "H". }
    iIntros (v).
    iModIntro.
    iIntros "#Hv R".
    subst K.
    simpl.
    unfold clwp.
    iIntros (Tκ TΨ) "TH".
    rewrite LET_Val.
    subst F.
    cbn [ofe_mor_car].
    do 2 rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ'') "[>Hlc [Hs Hh]]" "Hcl".
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    set (l:=Loc.fresh (dom σ'')).
    iExists σ'', l, _, (`Tκ (`κ (Ret l))).
    iFrame "Hs".
    simpl. change (Loc.fresh (dom σ'')) with l.
    iSplit; first done.
    iSplit.
    { simpl. rewrite ofe_iso_21. done. }
    iNext. iIntros "Hlc Hs".
    iMod (istate_alloc _ (IT_of_V v) l with "Hh") as "[Hh Hl]".
    {
      apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite -(Loc.add_0 l). apply Loc.fresh_fresh. lia.
    }
    iMod (inv_alloc (logN.@l) _
            (∃ βv : ITV, pointsto l (IT_of_V βv) ∗ interp_ty τ βv) with "[Hl Hv]")
      as "#HN".
    {
      iNext.
      iExists v.
      iFrame.
      iFrame "Hv".
    }
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iSpecialize ("W" $! (RetV l) with "[]").
    {
      iExists l.
      iSplit; first done.
      iApply "HN".
    }
    iModIntro.
    iApply ("W" with "R").
    iApply "TH".
  Qed.

  Lemma compat_assign {S : Set} {Ω : S → ty}
    τ e1 e2
    : validG Ω (interp_expr rs e1) (tRef τ)
      -∗ validG Ω (interp_expr rs e2) τ
      -∗ validG Ω (interp_expr rs (Assign e1 e2)) tUnit.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ σ) "#Hheap R #Hκ".
    simpl.
    match goal with
    | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ LET ?a) ?b] =>
        set (F := b)
    end.
    unshelve eset (K := HOM_compose κ (exist _ (LETCTX F) _ : HOM)).
    { apply _. }
    iSpecialize ("G" $! γ with "Hγ").
    iSpecialize ("G" $! K with "Hheap R []"); first last.
    { subst K; simpl; iApply "G". }
    iIntros (v).
    iModIntro.
    iIntros "#Hv R".
    subst K.
    simpl.
    unfold clwp.
    iIntros (Tκ TΨ) "TH".
    rewrite LET_Val.
    subst F.
    simpl.
    match goal with
    | |- context G [get_ret ?a] =>
          set (F := a)
    end.
    unshelve eset (K := HOM_compose κ (exist _ (get_ret F) _) : HOM).
    { apply _. }
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! K with "Hheap R []"); first last.
    { subst K; simpl; iApply "H". iApply "TH". }
    iIntros (w).
    iModIntro.
    subst K F.
    simpl.
    iIntros "(%l & #HEQ & Hw) R".
    iRewrite "HEQ".
    unfold clwp.
    iIntros (Tκ' TΨ') "TH'".
    rewrite IT_of_V_Ret.
    rewrite get_ret_ret.
    simpl.
    do 2 rewrite hom_vis.

    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ''') "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken (⊤ ∖ nclose (nroot.@"storeE"))).
    { set_solver. }
    iIntros "Hwk".
    iInv (logN.@l) as "H" "Hcl'".
    iAssert (▷ ⌜is_Some (σ''' !! l)⌝)%I as "#Hdom".
    {
      iNext.
      iDestruct "H" as "(%βv & Hp & H)".
      iApply (istate_loc_dom with "Hh Hp").
    }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [α' Ha'].
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iExists σ''', (), (<[l:=Next (IT_of_V v)]>σ'''), (`Tκ' (`κ (Ret ()))).
    iFrame "Hs".
    iSimpl. repeat iSplit; [done | done | ].
    iNext. iIntros "Hlc".
    iDestruct "H" as "(%βv & Hp & H)".
    iMod (istate_write _ _ (IT_of_V βv) (IT_of_V v) with "Hh Hp") as "[Hh Hp]".
    iIntros "Hs".
    iMod ("Hcl'" with "[Hp]") as "_".
    {
      iNext.
      iExists v.
      iFrame.
      iFrame "Hv".
    }
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iModIntro.
    rewrite <-IT_of_V_Ret.
    iApply ("Hκ" with "[] R"); first done.
    iApply "TH'".
  Qed.

  Lemma compat_deref {S : Set} (Ω : S → ty)
    τ e
    : validG Ω (interp_expr rs e) (tRef τ)
      -∗ validG Ω (interp_expr rs (Deref e)) τ.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ Q) "#Hheap R #Hκ".
    simpl.
    match goal with
    | |- context G [get_ret ?a] =>
          set (F := a)
    end.
    unshelve eset (K := HOM_compose κ (exist _ (get_ret F) _) : HOM).
    { apply _. }
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! K with "Hheap R []"); first last.
    { subst K; simpl; iApply "H". }
    iIntros (w).
    iModIntro.
    iIntros "#Hw R".
    subst K F.
    simpl.
    iDestruct "Hw" as "(%l & #HEQ & Hw)".
    iRewrite "HEQ".
    unfold clwp.
    iIntros (Tκ TΨ) "TH".
    rewrite IT_of_V_Ret.
    rewrite get_ret_ret.
    simpl.
    do 2 rewrite hom_vis.

    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ'') "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken (⊤ ∖ nclose (nroot.@"storeE"))).
    { set_solver. }
    iIntros "Hwk".
    iInv (logN.@l) as "H" "Hcl'".
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iDestruct "H" as "(%βv & Hp & #H)".
    iAssert (⌜is_Some (σ'' !! l)⌝)%I as "%Hdom".
    { iApply (istate_loc_dom with "Hh Hp"). }
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [β' Hb'].
    iAssert ((σ'' !! l ≡ Some (Next (IT_of_V βv))))%I as "#Hlookup".
    { iApply (istate_read with "Hh Hp"). }
    iAssert (▷ (β' ≡ IT_of_V βv))%I as "#Hba".
    { rewrite Hx. rewrite option_equivI.
      rewrite Hb'. by iNext. }
    iClear "Hlookup".
    iExists σ'', (Next β'), σ'', (`Tκ (`κ β')).
    iFrame "Hs".
    iSimpl. repeat iSplit; [ | | ].
    { by rewrite Hx /= Hb'. }
    {
      iPureIntro.
      rewrite ofe_iso_21.
      reflexivity.
    }
    iNext. iIntros "Hlc".
    iIntros "Hσ".
    iMod ("Hcl'" with "[Hp H]") as "_".
    {
      iNext.
      iExists βv.
      iFrame.
      iFrame "H".
    }
    iMod ("Hcl" with "[Hlc Hh Hσ]") as "_".
    { iNext. iExists _. iFrame. }
    iModIntro.
    iRewrite "Hba".
    iApply ("Hκ" with "H R").
    iApply "TH".
  Qed.

  Lemma compat_natop {S : Set}
    (Ω : S → ty)
    op α β :
    ⊢ validG Ω α tNat
      -∗ validG Ω β tNat
      -∗ validG Ω (interp_natop _ op α β) tNat.
  Proof.
    iIntros "#H #G".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ Q) "#Q R #W".
    simpl.

    set (K' := (NatOpRSCtx_HOM op α γ)).
    assert ((NATOP (do_natop op) (α γ) (β γ)) = ((`K') (β γ))) as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ K')). rewrite (HOM_compose_ccompose κ K' sss)//.

    iSpecialize ("G" $! γ with "Hγ").
    iSpecialize ("G" $! sss).
    iApply ("G" with "Q R []").
    iClear "G".
    iIntros (v).
    iModIntro.
    iIntros "#Hv R".
    simpl.
    clear K' sss.

    pose (K' := (NatOpLSCtx_HOM op (IT_of_V v) γ _)).
    assert ((NATOP (do_natop op) (α γ) (IT_of_V v)) = ((`K') (α γ)))
      as -> by done.
    rewrite HOM_ccompose.
    pose (sss := (HOM_compose κ K')). rewrite (HOM_compose_ccompose κ K' sss)//.

    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("H" $! sss).
    iApply ("H" with "Q R []").
    iIntros (w).
    iModIntro.
    iIntros "#Hw R".
    simpl.

    iDestruct "Hv" as "(%n & #HEQ)".
    iDestruct "Hw" as "(%n' & #HEQ')".
    iAssert ((NATOP (do_natop op) (IT_of_V w) (IT_of_V v))
               ≡ (Ret (do_natop op n' n)))%I as "#HEQ''".
    {
      iRewrite "HEQ".
      rewrite IT_of_V_Ret.
      iAssert ((IT_of_V w) ≡ IT_of_V (RetV n'))%I as "#HEQ2''".
      {
        iApply f_equivI.
        iApply "HEQ'".
      }
      rewrite IT_of_V_Ret.
      iAssert (NATOP (do_natop op) (IT_of_V w) (Ret n)
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
    iRewrite "HEQ''".
    iIntros (Tκ TΨ) "TH".
    rewrite <-IT_of_V_Ret.
    iApply ("W" with "[] R").
    - by iExists _.
    - iApply "TH".
  Qed.

  Lemma compat_lam {S : Set} (Ω : S → ty)
    (e : expr (inc S))
    (τ1 τ2 : ty)
    : ⊢ validG (Ω ▹ τ1) (interp_expr rs e) τ2 -∗ validG Ω (interp_expr rs (LamV e)) (tArr τ1 τ2).
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    iIntros (κ Q) "#Q R #W".
    cbn [interp_expr].
    unfold interp_lam.
    cbn [ofe_mor_car].
    match goal with
    | |- context G [ofe_mor_car _ _ Fun ?a] =>
        set (F := a)
    end.
    assert (Fun F ≡ IT_of_V $ FunV F)%stdpp as ->.
    { reflexivity. }
    iApply ("W" with "[] R").
    iExists _.
    iSplit; first done.
    iModIntro.
    iIntros (v) "#Hv".
    fold (interp_ty τ1).
    fold (interp_ty τ2).
    iIntros (κ' Q') "#Hκ'".
    rewrite APP'_Fun_l.
    rewrite laterO_map_Next.
    rewrite <-Tick_eq.
    iSpecialize ("H" $! (extend_scope γ (IT_of_V v)) with "[]").
    {
      iIntros ([| x]); iModIntro.
      - iIntros (κ'' Ψ'') "Q' R Hκ''".
        iApply ("Hκ''" with "Hv R").
      - iIntros (κ'' Ψ'') "Q' R #Hκ''".
        iApply ("Hγ" with "Q' R Hκ''").
    }
    subst F.
    cbn [later_car].
    cbn [ofe_mor_car].
    rewrite hom_tick.
    unfold obs_ref.
    cbn [ofe_mor_car].
    iIntros "R".
    iIntros (Tκ TΨ) "TH".
    rewrite hom_tick.
    iApply wp_tick.
    iNext.
    unfold interp_exprG.
    cbn [ofe_mor_car].
    iSpecialize ("H" $! κ' Q' with "Q R [Hκ']").
    - unfold obs_ref.
      cbn [ofe_mor_car].
      iApply "Hκ'".
    - iApply "H".
      iApply "TH".
  Qed.

  Fixpoint fl {S : Set} (Ω : S → ty) (e : expr S) (τ : ty) (H : typed_glued Ω e τ)
    : ⊢ validG Ω (interp_expr _ e) τ.
  Proof.
    destruct H.
    - by iApply compat_glueNat.
    - iApply compat_var.
    - iApply compat_app;
        [by iApply fl | by iApply fl].
    - iApply compat_alloc; by iApply fl.
    - iApply compat_assign;
        [by iApply fl | by iApply fl].
    - iApply compat_deref; by iApply fl.
    - iApply compat_nat.
    - iApply compat_unit.
    - iApply compat_lam; by iApply fl.
    - iApply compat_natop;
        [by iApply fl | by iApply fl].
  Qed.

  Lemma compat_HOM_id P:
    ⊢ logrel_ectx P P HOM_id.
  Proof.
    iIntros (v).
    iModIntro.
    iIntros "Pv R".
    simpl.
    unfold logpred.logrel_mcont'.
    simpl.
    iIntros (Tκ TΨ) "TH".
    by iApply "TH".
  Qed.

End sets.

Local Definition rs : gReifiers CtxDep 2 :=
  gReifiers_cons reify_delim (gReifiers_cons (sReifier_NotCtxDep_min reify_store CtxDep) gReifiers_nil).

Variable Hdisj : ∀ (Σ : gFunctors) (P Q : iProp Σ), disjunction_property P Q.

Lemma logpred_adequacy cr Σ R `{!Cofe R, SubOfe natO R, SubOfe unitO R, SubOfe locO R}
  `{!invGpreS Σ} `{!heapPreG rs R Σ} `{!statePreG rs R Σ}
  (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R)
  (e : IT (gReifiers_ops rs) R) st' k τ :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ},
      (£ cr ⊢ validG rs □ α τ)%I) →
  ssteps (gReifiers_sReifier rs) (α ı_scope) ([], (empty, ())) e st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) e st' β1 st1)
   ∨ (∃ βv, (IT_of_V βv ≡ e)%stdpp).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V e) as [βv|] eqn:Hb.
  { right. exists βv. apply IT_of_to_V'. rewrite Hb; eauto. }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) e st' β1 st1)
      ∨ (∃ e', (e ≡ Err e')%stdpp ∧ notStuck e')).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety (S cr)); eauto.
  { apply Hdisj. }
  { by rewrite Hb. }
  intros H2 H3.
  eexists (λ _, True)%I. split.
  { apply _. }
  iIntros "[[Hone Hcr] Hst]".
  match goal with
  | |- context G [has_full_state ?a] =>
      set (st := a)
  end.
  pose (cont_stack := st.1).
  pose (heap := st.2.1).
  iMod (new_heapG rs heap) as (H4) "H".
  iAssert (has_substate (cont_stack : delim.stateF ♯ _) ∗ has_substate heap)%I with "[Hst]" as "[Hcont Hheap]".
  { unfold has_substate, has_full_state.
    assert (of_state rs (IT (gReifiers_ops rs) _) st ≡
            of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state (cont_stack : delim.stateF ♯ _))
            ⋅ of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state heap))%stdpp as ->; last first.
    { rewrite -own_op. done. }
    unfold sR_idx. simpl.
    intro j.
    rewrite discrete_fun_lookup_op.
    inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 0%fin)). done. }
    intros j. inv_fin j.
    { unfold of_state, of_idx. simpl.
      erewrite (eq_pi _ _ _ (@eq_refl _ 1%fin)). done. }
    intros i. inversion i.
  }
  iApply fupd_wp.
  iMod (inv_alloc (nroot.@"storeE") _ (∃ σ, £ 1 ∗ has_substate σ ∗ own (heapG_name rs) (●V σ))%I with "[-Hcr Hcont]") as "#Hinv".
  { iNext. iExists _. iFrame. }
  simpl.
  iPoseProof (@Hlog _ _ _ with "Hcr") as "#Hlog".
  iSpecialize ("Hlog" $! ı_scope with "[]").
  { iIntros ([]). }
  unfold interp_exprG.
  simpl.
  iSpecialize ("Hlog" $! HOM_id (interp_ty rs τ) with "Hinv Hcont []").
  { iApply compat_HOM_id.  }
  iModIntro.
  iSpecialize ("Hlog" $! HOM_id (interp_ty rs τ) with "[]").
  {
    iIntros "%w Hw".
    iApply wp_val.
    by iModIntro.
  }
  iApply (wp_wand with "Hlog").
  iIntros (?) "_".
  by iModIntro.
Qed.

Lemma safety τ e σ (β : IT (sReifier_ops (gReifiers_sReifier rs)) (sumO natO (sumO unitO locO))) k :
  typed_glued □ e τ →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) ([], (empty, ())) β σ k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β σ β1 st1)
   ∨ (∃ βv, IT_of_V βv ≡ β)%stdpp.
Proof.
  intros Htyped Hsteps.
  pose (R := (sumO natO (sumO unitO locO))).
  pose (Σ := gFunctors.app invΣ (gFunctors.app (stateΣ rs R) (gFunctors.app (heapΣ rs R) gFunctors.nil))).
  assert (invGpreS Σ).
  { apply _. }
  assert (statePreG rs R Σ).
  { apply _. }
  assert (heapPreG rs R Σ).
  { apply _. }
  eapply (logpred_adequacy 0 Σ); eauto.
  intros ? ? ?. iIntros "_".
  by iApply fl.
Qed.
