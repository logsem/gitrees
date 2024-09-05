From gitrees Require Export prelude gitree lang_generic hom.
From stdpp Require Import gmap.
From gitrees.effects Require Import delim store.
From gitrees.examples.delim_lang Require Import lang interp typing hom clwp.
From gitrees.examples.delim_lang Require Import program_logic.weakestpre.
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
  Definition emap {A B : Set} := lang.emap (A := A) (B := B).
  Definition emap_id := lang.emap_id.
  Definition emap_comp := lang.emap_comp.
  Global Instance FMap_expr : FunctorCore lang.expr := lang.FMap_expr.
  Global Instance Functor_expr : Functor lang.expr := lang.Functor_expr.
End embed_lang.

Section syntax.

  Definition loc : Set := locations.loc.
  Global Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

  Inductive expr {X : Set} :=
  | Var (x : X) : expr
  | App (e₁ : expr) (e₂ : expr) : expr
  | LamV (e : @expr (inc X))
  | NatOp (op : lang.nat_op) (e₁ : expr) (e₂ : expr) : expr
  | Alloc (e : expr) : expr
  | Assign (e₁ e₂ : expr) : expr
  | Deref (e : expr) : expr
  | LocV (l : loc)
  | UnitV
  | LitV (n : nat)
  | Embed : embed_lang.expr ∅ → expr.

  Arguments expr X%bind : clear implicits.
  Local Open Scope bind_scope.

  Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
    match e with
    | Var x => Var (f x)
    | App e₁ e₂ => App (emap f e₁) (emap f e₂)
    | LamV e => LamV (emap (f ↑) e)
    | NatOp o e₁ e₂ => NatOp o (emap f e₁) (emap f e₂)
    | Alloc e => Alloc (emap f e)
    | Assign e₁ e₂ => Assign (emap f e₁) (emap f e₂)
    | Deref e => Deref (emap f e)
    | LocV l => LocV l
    | UnitV => UnitV
    | LitV n => LitV n
    | Embed e => Embed e
    end.

  Global Instance FMap_expr : FunctorCore expr := @emap.

  Fixpoint emap_id X (δ : X [→] X) (e : expr X) : δ ≡ ı → fmap δ e = e.
  Proof.
    - auto_map_id.
  Qed.

  Fixpoint emap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : expr A) :
    f ∘ g ≡ h → fmap f (fmap g e) = fmap h e.
  Proof.
    - auto_map_comp.
  Qed.

  Global Instance Functor_expr : Functor expr.
  Proof.
    split; [exact emap_id | exact emap_comp].
  Qed.

End syntax.

Arguments expr X%bind : clear implicits.

Section typing.

  Inductive ty :=
  | tNat
  | tUnit
  | tArr (τ1 τ2 : ty)
  | tRef (τ : ty).

  (* Inductive type_translate : ty → embed_lang.ty → Type := *)
  (* | TT_nat : type_translate tNat Tnat *)
  (* | TT_arr τ τ' α α' σ σ' β β' : type_translate τ τ' *)
  (*                                → type_translate α α' *)
  (*                                → type_translate σ σ' *)
  (*                                → type_translate β β' *)
  (*                                → type_translate (tArr τ (tArr (tArr σ α) β)) *)
  (*                                    (Tarr τ' α' σ' β'). *)


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
      LET (t1 env) $ λne f,
      LET (t2 env) $ λne x,
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

  Program Definition interp_natop {A} (op : lang.nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
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

  Fixpoint interp_expr_ren {S S'} env
    (δ : S [→] S') (e : expr S) :
    (interp_expr (fmap δ e) env ≡ interp_expr e (ren_scope δ env))%stdpp.
  Proof.
    destruct e; simpl; try by repeat f_equiv.
    - f_equiv.
      + f_equiv. apply interp_expr_ren.
      + intro; simpl.
        f_equiv; by rewrite interp_expr_ren.
    - f_equiv. intro. simpl. rewrite interp_expr_ren.
      f_equiv.
      intros [| ?]; simpl; first done.
      reflexivity.
    - f_equiv.
      + f_equiv. apply interp_expr_ren.
      + intro; simpl.
        f_equiv; by rewrite interp_expr_ren.
  Qed.

  Section example.

    Program Definition letE {S : Set} (e1 : expr S) (e2 : expr (inc S)) : expr S :=
      App (LamV e2) e1.

    Program Definition seqE {S : Set} (e1 : expr S) (e2 : expr S) : expr S :=
      letE e1 (shift e2).

    Program Definition Awkward : expr ∅ :=
      letE (Alloc (LitV 0)) (LamV (seqE (Assign (Var (VS VZ)) (LitV 1))
                                     (seqE (App (Var VZ) UnitV)
                                        (Deref (Var (VS VZ)))))).

  End example.

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
      (CLWP@{rs} α {{ βv, Ψ βv ∗ has_substate ([] : delim.stateF ♯ IT) }})%I.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    unfold clwp.
    f_equiv; intro; simpl.
    f_equiv; intro; simpl.
    by do 6 f_equiv.
  Qed.

  Program Definition interp_exprG V : IT -n> iProp :=
    λne e, (heap_ctx rs
            -∗ has_substate ([] : delim.stateF ♯ IT)
            -∗ obs_ref V e)%I.
  Next Obligation.
    solve_proper.
  Qed.

  Local Instance interp_exprG_ne : NonExpansive interp_exprG.
  Proof.
    solve_proper_prepare.
    do 3 f_equiv.
    solve_proper.
  Qed.

  Local Instance interp_exprG_bind_ne (κ : HOM) (Φ : ITV -n> iProp)
    : NonExpansive (λ βv, (interp_exprG Φ (`κ (IT_of_V βv)))%I).
  Proof.
    solve_proper.
  Qed.

  Lemma interp_exprG_bind (κ : HOM) e (Φ : ITV -n> iProp) :
    interp_exprG (λne βv, interp_exprG Φ (`κ (IT_of_V βv))) e ⊢ interp_exprG Φ (`κ e).
  Proof.
    iIntros "H".
    iIntros "#Hheap Hst".
    iApply clwp_bind.
    iSpecialize ("H" with "Hheap Hst").
    unfold interp_exprG, obs_ref.
    cbn [ofe_mor_car].
    rewrite /clwp.
    iIntros "%K %Ψ G".
    iSpecialize ("H" $! K Ψ with "[G]").
    {
      iIntros "%v [H1 H2]".
      iApply "G".
      by iApply "H1".
    }
    iApply "H".
  Qed.

  Lemma interp_exprG_val (Φ : ITV -n> iProp) (e : IT) (v : ITV) `{!IntoVal e v} :
    Φ v ⊢ interp_exprG Φ e.
  Proof.
    iIntros "H #Hheap Hctx".
    rewrite <-into_val.
    iApply clwp_value_fupd'.
    iModIntro.
    iFrame.
  Qed.

  Lemma interp_exprG_tick (Φ : ITV -n> iProp) (e : IT) :
    ▷ interp_exprG Φ e ⊢ interp_exprG Φ (Tick e).
  Proof.
    iIntros "H #Hheap Hctx".
    rewrite /obs_ref /clwp /=.
    iIntros "%K %Ψ G".
    rewrite hom_tick.
    iApply wp_tick.
    iNext.
    iSpecialize ("H" with "Hheap Hctx").
    rewrite /clwp /=.
    iSpecialize ("H" $! K).
    iApply "H".
    iApply "G".
  Qed.

  Lemma interp_exprG_mono (Φ Ψ : ITV -n> iProp) (e : IT) :
    interp_exprG Φ e -∗ (∀ v, Φ v -∗ Ψ v) -∗ interp_exprG Ψ e.
  Proof.
    iIntros "H G #Hheap Hctx".
    rewrite /obs_ref /=.
    iApply (clwp_mono with "[H Hctx] [G]").
    { by iApply "H". }
    iIntros (v) "(H1 & H2)".
    iModIntro.
    iFrame "H2".
    by iApply "G".
  Qed.

  Program Definition interp_tarr (Φ1 Φ2 : ITV -n> iProp)
    : ITV -n> iProp :=
    λne αv,
      (∃ f',
         IT_of_V αv ≡ Fun f'
         ∧ □ ∀ βv, Φ1 βv -∗ interp_exprG Φ2 ((Fun f') ⊙ ((IT_of_V βv))))%I.
  Solve All Obligations with solve_proper_please.

  Opaque interp_exprG.

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
    iApply interp_exprG_val.
    by iExists _.
  Qed.

  Lemma compat_unit {S : Set} (Ω : S → ty) :
    ⊢ validG Ω (interp_unit rs) tUnit.
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    by iApply interp_exprG_val.
  Qed.

  Lemma compat_var {S : Set} (Ω : S → ty) (v : S) :
    ⊢ validG Ω (interp_var v) (Ω v).
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    iApply "H".
  Qed.

  Lemma compat_glueNat {S : Set} (Ω : S → ty)
    (e : lang.expr ∅)
    (t : embed_lang.typed_expr_pure □ e ℕ)
    : ⊢ validG Ω (interp_expr rs (Embed e)) tNat.
  Proof.
    iModIntro.
    iIntros (γ) "#H".
    iIntros "#Q R".
    unfold obs_ref.
    cbn [ofe_mor_car].
    rewrite /clwp.
    iIntros "%K %Ψ HHH".
    iPoseProof (logpred.fundamental_expr_pure rs □ ℕ e t) as "#G".
    unshelve iSpecialize ("G" $! ı_scope _).
    { iIntros ([]). }
    iApply (wp_reset with "R").
    iIntros "!> _ R".
    unfold logpred.logrel_pure.
    cbn [ofe_mor_car].
    unfold logpred.logrel_expr.
    cbn [ofe_mor_car].
    unfold logpred.obs_ref.
    cbn [ofe_mor_car].
    iSpecialize ("G" $! (interp_ty tNat) logpred.𝒫_HOM with "[]").
    { iIntros (αv) "!> #Hαv %F %Q Hs Hss".
      by iApply "Hs".
    }
    iApply ("G" $! [laterO_map (`K)] Ψ with "[HHH] R").
    iIntros "%βv #Hβv R".
    iApply (wp_pop_cons with "R").
    iIntros "!> _ R".
    iApply "HHH".
    iFrame "R Hβv".
  Qed.

  (* Lemma compat_glue {S : Set} (Ω : S → ty) *)
  (*   τ τ' *)
  (*   (H : type_translate τ τ') *)
  (*   (e : ITV) *)
  (*   : ⊢ interp_ty τ e ∗-∗ logpred.interp_ty rs τ' e. *)
  (* Proof. *)
  (*   revert e. *)
  (*   induction H; intros e. *)
  (*   - iSplit; iIntros "H"; iApply "H". *)
  (*   - iSplit; iIntros "H". *)
  (*     + iDestruct "H" as "(%f' & ? & #J)". *)
  (*       iExists f'. *)
  (*       iSplit; first done. *)
  (*       iModIntro. *)
  (*       iIntros (βv) "Hβv %κ #Hκ %st %Q Hm Hst". *)
  (*       simpl. *)
  (*       iSpecialize ("J" $! βv with "[Hβv]"). *)
  (*       * iApply IHtype_translate1. *)
  (*         iApply "Hβv". *)
  (*       * iApply ("J" $! _ _ κ Q with ""). *)
  (*         iModIntro. *)
  (*         iIntros (v) "(#Hv & Hst)". *)
  (*         iSpecialize ("Hκ" $! v with "[]"). *)
  (*         --  *)
  (*         -- iSpecialize ("Hκ" $! [] Q with "[]"). *)
  (*            ++ admit. *)
  (*            ++ by iApply "Hκ". *)
  (*     + admit. *)
  (*         iApply "Hκ". *)
  (*     iDestruct open_constr as % simple_intropattern *)

  (* Lemma compat_glue {S : Set} (Ω : S → ty) *)
  (*    τ τ' *)
  (*    (H : type_translate τ τ') *)
  (*    (e : lang.expr ∅) *)
  (*    (t : embed_lang.typed_expr_pure □ e τ') *)
  (*   : ⊢ validG Ω (constO $ (RESET ◎ NextO) (embed_lang.interp_closed  _ e)) τ. *)
  (* Proof. *)
  (*   revert e t. *)
  (*   induction H; intros e t. *)
  (*   - iApply compat_glueNat. *)
  (*     done. *)
  (*   - iModIntro. *)
  (*     iIntros (γ) "#H". *)
  (*     iIntros "#Q R". *)
  (*     unfold obs_ref. *)
  (*     cbn [ofe_mor_car]. *)
  (*     iIntros "%K %Ψ #HHH". *)
  (*     iApply (wp_reset with "R"). *)
  (*     iIntros "!> _ R". *)
  (*     iPoseProof (logpred.fundamental_expr_pure rs □ _ e t) as "#G". *)
  (*     unshelve iSpecialize ("G" $! ı_scope _). *)
  (*     { iIntros ([]). } *)
  (*     simpl. *)
  (*     iSpecialize ("G" $! _ logpred.𝒫_HOM with "[]"). *)
  (*     { iIntros (αv) "!> #Hαv %F %Q Hs Hss". *)
  (*       by iApply "Hs". *)
  (*     } *)
  (*     iApply ("G" $! [laterO_map (`K)] Ψ with "[] R"); iClear "G". *)
  (*     iIntros "%βv #Hβv R". *)
  (*     iApply (wp_pop_cons with "R"). *)
  (*     iIntros "!> _ R". *)
  (*     iApply "HHH"; iClear "HHH". *)
  (*     simpl. *)
  (*     unfold logpred.logrel_arr'. *)
  (*     iDestruct "Hβv" as "(%f' & ? & #J)". *)
  (*     iFrame "R". *)
  (*     iExists f'. *)
  (*     iSplit; first done. *)
  (*     iModIntro. *)
  (*     iIntros (aaa) "#Haaa". *)
  (*     iSpecialize ("J" $! aaa). *)



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

    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("G" $! γ with "Hγ").
    iClear "Hγ".

    set (K := (AppLSCtx_HOM β γ)).
    assert ((interp_app rs α β γ)
              ≡ `K (α γ))%stdpp as ->.
    { simpl; do 3 (f_equiv; intro; simpl). }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "H"); iClear "H".
    iIntros (w) "#H".
    rewrite /= LET_Val /=.
    clear K.
    set (K := (AppRSCtx_HOM (IT_of_V w) γ _)).
    assert (LET _ _ ≡ `K (β γ))%stdpp as ->;
                                           first by rewrite /= LET_Val /=.
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "G"); iClear "G".
    iIntros (v) "#G".
    rewrite /= LET_Val /= LET_Val /=.
    iDestruct "H" as "(%f & #HEQ & #Hw)".
    iAssert ((IT_of_V w ⊙ (IT_of_V v)) ≡ (Fun f ⊙ (IT_of_V v)))%I as "HEQ'".
    {
      iApply (f_equivI (flipO APP' (IT_of_V v))).
      iApply "HEQ".
    }
    iRewrite "HEQ'".
    iApply ("Hw" $! v with "G").
  Qed.

  Lemma compat_alloc {S : Set}
    (Ω : S → ty)
    (τ : ty)
    (e : expr S) :
    ⊢ validG Ω (interp_expr rs e) τ
      -∗ validG Ω (interp_expr rs (Alloc e)) (tRef τ).
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    iSpecialize ("H" $! γ with "Hγ").
    iClear "Hγ".
    unshelve eset (K := exist _ (λne v, interp_alloc (R := R) rs (constO v) γ) _ : HOM).
    1-3: apply _.
    { solve_proper. }
    { simpl; apply _. }
    assert ((interp_expr rs (Alloc e) γ)
              ≡ `K (interp_expr rs e γ))%stdpp as ->.
    { reflexivity. }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "H"); iClear "H".
    iIntros (w) "#H".
    subst K; simpl.
    rewrite LET_Val /=.
    iIntros "Hheap Hctx".
    rewrite /obs_ref /clwp /=.
    iIntros "%κ' %Ψ' G".
    iApply (wp_alloc_hom with "Hheap").
    iIntros (l).
    do 2 iNext.
    iIntros "Hl".
    iApply fupd_wp.
    iMod (inv_alloc (logN.@l) ⊤
                 (∃ βv : ITV, pointsto l (IT_of_V βv) ∗ interp_ty τ βv) with "[Hl H]")
      as "HN".
    {
      iNext.
      iExists w.
      by iFrame.
    }
    iSpecialize ("G" $! (RetV l) with "[Hctx HN]").
    {
      iFrame "Hctx".
      iExists l.
      iSplit; first done.
      iFrame "HN".
    }
    iModIntro.
    iApply "G".
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
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("G" $! γ with "Hγ").
    iClear "Hγ".
    unshelve eset (K := exist _
                          (λne v, interp_assign (R := R) rs
                                    (interp_expr rs e1) (constO v) γ) _ : HOM).
    1-8: apply _.
    { solve_proper. }
    { simpl; apply _. }
    assert ((interp_expr rs (Assign e1 e2) γ)
              ≡ `K (interp_expr rs e2 γ))%stdpp as ->.
    { reflexivity. }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "G"); iClear "G".
    iIntros (v) "#G".
    rewrite /= LET_Val /=.
    clear K.
    unshelve eset (K := exist _
                          (λne w, (get_ret (λne l : loc, WRITE l (IT_of_V v)) w)) _ : HOM).
    { simpl; apply _. }
    match goal with
    | |- context G [ofe_mor_car _ _ (interp_exprG interp_tunit) ?a] =>
        assert (a
              ≡ `K (interp_expr rs e1 γ))%stdpp as ->
    end.
    {
      simpl.
      f_equiv.
      f_equiv; intro; simpl.
      f_equiv.
    }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "H"); iClear "H".
    iIntros (w) "#H".
    simpl.
    clear K.
    iDestruct "H" as "(%l & #HEQ & Hw)".
    iRewrite "HEQ".
    rewrite IT_of_V_Ret.
    rewrite get_ret_ret.
    simpl.
    iIntros "Hheap Hctx".
    rewrite /obs_ref /clwp /=.
    iIntros "%κ' %Ψ Hκ'".
    iApply (wp_write_atomic_hom _ _ _ _ with "Hheap"); first last.
    {
      iInv (logN.@l) as "H" "Hcl'".
      iDestruct (bi.later_exist with "H") as "(%βv & H)".
      iDestruct (bi.later_sep with "H") as "(H1 & #H2)".
      iExists (IT_of_V βv).
      iFrame "H1".
      iModIntro.
      do 2 iNext.
      iIntros "H".
      iMod ("Hcl'" with "[H]").
      {
        iNext.
        iExists v.
        iFrame "H G".
      }
      iModIntro.
      iApply ("Hκ'" $! (RetV ())).
      iFrame "Hctx".
      done.
    }
    apply ndot_preserve_disjoint_r.
    apply ndot_ne_disjoint.
    done.
  Qed.

  Lemma compat_deref {S : Set} (Ω : S → ty)
    τ e
    : validG Ω (interp_expr rs e) (tRef τ)
      -∗ validG Ω (interp_expr rs (Deref e)) τ.
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    iSpecialize ("H" $! γ with "Hγ").
    iClear "Hγ".
    unshelve eset (K := exist _
                          (λne v, interp_deref (R := R) rs (constO v) γ) _ : HOM).
    1-3: apply _.
    { solve_proper. }
    { simpl; apply _. }
    assert ((interp_expr rs (Deref e) γ)
              ≡ `K (interp_expr rs e γ))%stdpp as ->.
    { reflexivity. }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "H"); iClear "H".
    iIntros (v) "#H".
    iDestruct "H" as "(%l & #HEQ & Hw)".
    iRewrite "HEQ".
    rewrite /= IT_of_V_Ret.
    rewrite get_ret_ret.
    clear K.
    simpl.
    iIntros "Hheap Hctx".
    rewrite /obs_ref /clwp /=.
    iIntros "%κ %Ψ Hκ".
    iApply (wp_read_atomic_hom _ _ _ _ with "Hheap"); first last.
    {
      iInv (logN.@l) as "H" "Hcl'".
      iDestruct (bi.later_exist with "H") as "(%βv & H)".
      iDestruct (bi.later_sep with "H") as "(H1 & #H2)".
      iExists (IT_of_V βv).
      iFrame "H1".
      iModIntro.
      do 2 iNext.
      iIntros "H".
      iMod ("Hcl'" with "[H]").
      {
        iNext.
        iExists βv.
        iFrame "H H2".
      }
      iModIntro.
      iApply ("Hκ" with "[$H2 $Hctx]").
    }
    apply ndot_preserve_disjoint_r.
    apply ndot_ne_disjoint.
    done.
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
    iSpecialize ("H" $! γ with "Hγ").
    iSpecialize ("G" $! γ with "Hγ").
    iClear "Hγ".
    set (K := (NatOpRSCtx_HOM op α γ)).
    assert ((interp_natop rs op α β γ)
              ≡ `K (β γ))%stdpp as ->.
    { simpl; f_equiv. }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "G"); iClear "G".
    iIntros (v) "#G".
    subst K.
    simpl.
    assert (NATOP (do_natop op) (α γ) (IT_of_V v)
              ≡ (interp_natop rs op α (constO (IT_of_V v)) γ))%stdpp as ->.
    { simpl; do 3 (f_equiv; intro; simpl). }
    set (K' := (NatOpLSCtx_HOM op (IT_of_V v) γ _)).
    assert ((interp_natop rs op α (constO (IT_of_V v)) γ)
              ≡ `K' (α γ))%stdpp as ->.
    { simpl; do 3 (f_equiv; intro; simpl). }
    iApply interp_exprG_bind.
    iApply (interp_exprG_mono with "H"); iClear "H".
    iIntros (w) "#H".
    subst K'.
    simpl.
    iDestruct "G" as "(%n & #HEQ)".
    iDestruct "H" as "(%n' & #HEQ')".
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
    iApply interp_exprG_val.
    by iExists _.
  Qed.

  Lemma compat_lam {S : Set} (Ω : S → ty)
    (e : expr (inc S))
    (τ1 τ2 : ty)
    : ⊢ validG (Ω ▹ τ1) (interp_expr rs e) τ2
        -∗ validG Ω (interp_expr rs (LamV e)) (tArr τ1 τ2).
  Proof.
    iIntros "#H".
    iModIntro.
    iIntros (γ) "#Hγ".
    cbn [interp_expr].
    unfold interp_lam.
    cbn [ofe_mor_car].
    iApply interp_exprG_val.
    match goal with
    | |- context G [FunV ?a] =>
        set (F := a)
    end.
    iExists _.
    iSplit; first done.
    iModIntro.
    iIntros (v) "#Hv".
    fold (interp_ty τ1).
    fold (interp_ty τ2).
    rewrite APP'_Fun_l.
    rewrite laterO_map_Next.
    rewrite <-Tick_eq.
    iSpecialize ("H" $! (extend_scope γ (IT_of_V v)) with "[]").
    {
      iIntros ([| x]); iModIntro.
      - iIntros "Q' R".
        rewrite /obs_ref /clwp /=.
        iIntros "%κ'' %Ψ'' Hκ''".
        iApply ("Hκ''" with "[$Hv $R]").
      - iIntros "Q' R".
        rewrite /obs_ref /clwp /=.
        iIntros "%κ'' %Ψ'' Hκ''".
        iSpecialize ("Hγ" with "Q' R").
        rewrite /obs_ref /clwp /=.
        iApply ("Hγ" with "Hκ''").
    }
    subst F.
    simpl.
    iApply interp_exprG_tick.
    iNext.
    iFrame "H".
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

End sets.

Section example.
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

  Definition awkN : namespace := nroot .@ "awkN".

  Program Definition awk_inv (l : locO) : iProp :=
    (inv awkN ((pointsto l (Ret 0)) ∨ (pointsto l (Ret 1))))%I.

  Program Definition awkDenot : IT := interp_expr rs Awkward ı_scope.

  (* Program Definition awkPred : ITV -n> iProp *)
  (*   := λne βv, (∀ f : IT, (CLWP (f ⊙ (Ret ())) *)
  (*                                      {{ γv, IT_of_V γv ≡ Ret () }}) *)
  (*                                   -∗ CLWP (IT_of_V βv ⊙ f) *)
  (*                                        {{ αv, IT_of_V αv ≡ Ret 1 }})%I. *)
  (* Solve All Obligations with solve_proper. *)

  (* Lemma awkSpec : ⊢ CLWP awkDenot {{ awkPred }}. *)
  (* Proof. *)
  (* Admitted. *)

End example.

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
  iModIntro.
  iSpecialize ("Hlog" with "Hinv Hcont").
  rewrite /clwp /=.
  iApply ("Hlog" $! HOM_id (constO True%I)).
  iIntros "%w Hw".
  iApply wp_val.
  done.
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

Definition R := (sumO natO (sumO unitO locO)).

Lemma logpred_adequacy_nat Σ
  `{!invGpreS Σ} `{!heapPreG rs R Σ} `{!statePreG rs R Σ}
  (α : interp_scope ∅ -n> IT (gReifiers_ops rs) R)
  (e : IT (gReifiers_ops rs) R) st' k :
  (∀ `{H1 : !invGS Σ} `{H2: !stateG rs R Σ} `{H3: !heapG rs R Σ},
     (£ 1 ⊢ validG rs □ α tNat)%I) →
  ssteps (gReifiers_sReifier rs) (α ı_scope) ([], (empty, ())) e st' k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) e st' β1 st1)
  ∨ (∃ (n : natO), (IT_of_V (RetV n) ≡ e)%stdpp).
Proof.
  intros Hlog Hst.
  destruct (IT_to_V e) as [βv|] eqn:Hb.
  {
    unshelve epose proof (wp_adequacy 1 Σ _ _ rs (α ı_scope) ([], (∅%stdpp, ()))
                            βv st' notStuck k (λ x, ∃ n : natO, (RetV n) ≡ x)%stdpp _) as Had.
    {
      rewrite IT_of_to_V'.
      - apply Hst.
      - rewrite Hb.
        reflexivity.
    }
    right.
    simpl in Had.
    destruct Had as [n Had].
    - intros H2 H3.
      exists (interp_tnat rs).
      split; first solve_proper.
      split.
      + intros β.
        iIntros "(%n & #HEQ)".
        iExists n.
        iDestruct (internal_eq_sym with "HEQ") as "HEQ'"; iClear "HEQ".
        iAssert (IT_of_V β ≡ Ret n)%I as "#Hb".
        { iRewrite - "HEQ'". iPureIntro. by rewrite IT_of_V_Ret. }
        iAssert (⌜β ≡ RetV n⌝)%I with "[-]" as %Hfoo.
        {
          destruct β as [r|f]; simpl.
          - iPoseProof (Ret_inj' with "Hb") as "%Hr".
            iPureIntro.
            simpl in Hr.
            rewrite Hr.
            reflexivity.
          - iExFalso. iApply (IT_ret_fun_ne).
            iApply internal_eq_sym. iExact "Hb".
        }
        iPureIntro. rewrite Hfoo. reflexivity.
      + iIntros "[Hcr Hst]".
        match goal with
        | |- context G [has_full_state ?a] =>
            set (st := a)
        end.
        pose (cont_stack := st.1).
        iMod (new_heapG rs empty) as (H4) "H".
        specialize (Hlog H2 H3 H4).
        iPoseProof (Hlog with "Hcr") as "#G".
        iSpecialize ("G" $! ı_scope with "[]").
        { iIntros ([]). }
        iAssert (has_substate (cont_stack : delim.stateF ♯ _) ∗ has_substate empty)%I with "[Hst]" as "[Hcont Hheap]".
        { unfold has_substate, has_full_state.
          assert (of_state rs (IT (gReifiers_ops rs) _) st ≡
                    of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state (cont_stack : delim.stateF ♯ _))
                  ⋅ of_idx rs (IT (gReifiers_ops rs) _) sR_idx (sR_state empty))%stdpp as ->; last first.
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
        iMod (inv_alloc (nroot.@"storeE") _ (∃ σ, £ 1 ∗ has_substate σ ∗ own (heapG_name rs) (●V σ))%I with "[-Hcont]") as "#Hinv".
        { iNext. iExists _. iFrame. }
        iSpecialize ("G" with "Hinv Hcont").
        rewrite /obs_ref /clwp /=.
        iSpecialize ("G" $! HOM_id (interp_tnat rs)).
        iModIntro.
        iApply "G".
        iIntros (v) "(Hv & _)".
        iApply wp_val.
        by iModIntro.
    - exists n.
      rewrite Had.
      apply IT_of_to_V'.
      rewrite Hb.
      reflexivity.
  }
  left.
  cut ((∃ β1 st1, sstep (gReifiers_sReifier rs) e st' β1 st1)
      ∨ (∃ e', (e ≡ Err e')%stdpp ∧ notStuck e')).
  { intros [?|He]; first done.
    destruct He as [? [? []]]. }
  eapply (wp_safety (S 1)); eauto.
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
  iSpecialize ("Hlog" with "Hinv Hcont").
  iModIntro.
  rewrite /clwp /=.
  iApply ("Hlog" $! HOM_id (constO True%I)).
  iIntros "%w Hw".
  iApply wp_val.
  by iModIntro.
Qed.

Lemma safety_nat e σ (β : IT (sReifier_ops (gReifiers_sReifier rs)) (sumO natO (sumO unitO locO))) k :
  typed_glued □ e tNat →
  ssteps (gReifiers_sReifier rs) (interp_expr rs e ı_scope) ([], (empty, ())) β σ k →
  (∃ β1 st1, sstep (gReifiers_sReifier rs) β σ β1 st1)
   ∨ (∃ (n : natO), (IT_of_V (RetV n) ≡ β)%stdpp).
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
  eapply (logpred_adequacy_nat Σ); eauto.
  intros ? ? ?. iIntros "_".
  by iApply fl.
Qed.
