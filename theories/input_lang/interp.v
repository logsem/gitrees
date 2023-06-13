(** Interpretation and adequacy for the input_lang *)
From Equations Require Import Equations.
From gitrees Require Import gitree.
From gitrees.input_lang Require Import lang.

Notation stateO := (leibnizO state).

Program Definition inputE : opInterp :=  {|
  Ins := unitO;
  Outs := (natO)%OF;
|}.

Canonical Structure reify_input : sReifier.
Proof.
  simple refine {| sReifier_ops := inputE;
                   sReifier_state := stateO
                |}.
  intros X HX op.
  destruct op as []; simpl.
  simple refine (λne (us : prodO unitO stateO),
    Some $ update_input (sndO us) : optionO (prodO natO stateO)).
  intros n [[] s1] [[] s2] [_ Hs].
  repeat f_equiv. apply Hs.
Defined.


Section constructors.
  Context {E : opsInterp}.
  Context {subEff0 : subEff inputE E}.
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Definition INPUT : (natO -n> IT) -n> IT.
  Proof using E subEff0.
    simple refine (λne k, Vis (E:=E) (subEff_opid (()))
                            (subEff_conv_ins (F:=inputE) (op:=(())) ())
                            (NextO ◎ k ◎ subEff_conv_outs2 (F:=inputE) (op:=(())))).
    solve_proper.
  Defined.

End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_input rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Context `{!invGS_gen hlc Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_input (σ σ' : stateO) (n : nat) (k : natO -n> IT) Φ :
    update_input σ = (n, σ') →
    has_substate σ -∗
    ▷ (has_substate σ' -∗ WP@{rs} (k n) {{ Φ }}) -∗
    WP@{rs} (INPUT k) {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold INPUT. simpl.
    iApply (wp_subreify with "Hs").
    { simpl. by rewrite Hs. }
    { simpl. by rewrite ofe_iso_21. }
    iModIntro. done.
  Qed.

End weakestpre.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_input rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).


  Definition do_natop (op : nat_op) (x y : nat) : nat :=
    match op with
    | Add => x+y
    | Sub => x-y
    end.

  (** Interpreting individual operators *)
  Fixpoint interp_scope (S : scope) : ofe :=
    match S with
    | [] => unitO
    | τ::Sc => prodO IT (interp_scope Sc)
    end.

  Instance interp_scope_cofe S : Cofe (interp_scope S).
  Proof. induction S; simpl; apply _. Qed.

  Instance interp_scope_inhab S : Inhabited (interp_scope S).
  Proof. induction S; simpl; apply _. Defined.

  Equations interp_var {S : scope} (v : var S) : interp_scope S -n> IT :=
    interp_var (S:=(_::_))     Vz := fstO;
    interp_var (S:=(_::Sc)) (Vs v) := interp_var v ◎ sndO.

  Instance interp_var_ne S (v : var S) : NonExpansive (@interp_var S v).
  Proof.
    intros n D1 D2 HD12. induction v; simp interp_var.
    - by f_equiv.
    - eapply IHv. by f_equiv.
  Qed.

  Global Instance interp_var_proper S (v : var S) : Proper ((≡) ==> (≡)) (interp_var v).
  Proof. apply ne_proper. apply _. Qed.

  Program Definition interp_input {A} : A -n> IT :=
    λne env, INPUT Nat.

  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Next Obligation.
    repeat intro. repeat f_equiv; eauto.
  Qed.
  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof.
    unfold interp_natop. repeat intro. simpl.
    repeat f_equiv; eauto.
  Qed.
  Typeclasses Opaque interp_natop.

  Opaque laterO_map.
  Program Definition interp_rec_pre {A} (body : prodO IT (prodO IT A) -n> IT)
    : laterO (A -n> IT) -n> A -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : A -n> IT) (a : IT),
                                     body (self env,(a,env))) self.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    repeat intro. repeat f_equiv. solve_proper.
  Qed.
  Next Obligation.
    repeat intro. cbn-[laterO_map].
    by repeat f_equiv.
  Qed.

  Definition interp_rec {A} body : A -n> IT := mmuu (interp_rec_pre body).
  Program Definition ir_unf {A} (body : prodO IT (prodO IT A) -n> IT) env : IT -n> IT :=
    λne a, body (interp_rec body env, (a,env)).
  Next Obligation. solve_proper. Qed.

  Lemma interp_rec_unfold {A} (body : prodO IT (prodO IT A) -n> IT) env :
    interp_rec body env ≡ Fun $ Next $ ir_unf body env.
  Proof.
    trans (interp_rec_pre body (Next (interp_rec body)) env).
    { f_equiv. rewrite /interp_rec. apply mmuu_unfold. }
    simpl. rewrite laterO_map_Next. repeat f_equiv.
    simpl. unfold ir_unf. intro. simpl. reflexivity.
  Qed.

  Program Definition interp_app {A} (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, APP' (t1 env) (t2 env).
  Next Obligation.
    repeat intro. repeat f_equiv; eauto.
  Qed.
  Global Instance interp_app_ne A : NonExpansive2 (@interp_app A).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_app.

  Program Definition interp_if {A} (t0 t1 t2 : A -n> IT) : A -n> IT :=
    λne env, IF (t0 env) (t1 env) (t2 env).
  Next Obligation. solve_proper. Qed.
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Nat n.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | Lit n => interp_nat n
    | RecV e => interp_rec (interp_expr e)
    end
  with interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | Val v => interp_val v
    | Var x => interp_var x
    | Rec e => interp_rec (interp_expr e)
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
    | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
    | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
    | Input => interp_input
    end.

  Program Definition interp_ctx_item {S : scope} (K : ectx_item S) : interp_scope S -n> IT -n> IT :=
    match K with
    | AppLCtx v2 => λne env t, interp_app (constO t) (interp_val v2) env
    | AppRCtx e1 => λne env t, interp_app (interp_expr e1) (constO t) env
    | NatOpLCtx op v2 => λne env t, interp_natop op (constO t) (interp_val v2) env
    | NatOpRCtx op e1 => λne env t, interp_natop op (interp_expr e1) (constO t) env
    | IfCtx e1 e2 => λne env t, interp_if (constO t) (interp_expr e1) (interp_expr e2) env
    end.
  Opaque interp_app.
  Next Obligation. repeat intro; repeat f_equiv; eauto. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. repeat intro; repeat f_equiv; eauto. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. repeat intro; repeat f_equiv; eauto. Qed.
  Next Obligation.
    repeat intro; repeat f_equiv; eauto.
    intro. simpl. f_equiv; eauto; solve_proper.
  Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Transparent interp_app.

  #[global] Instance interp_val_asval {S} (v : val S) D : AsVal (interp_val v D).
  Proof.
    destruct v; simpl; first apply _.
    rewrite interp_rec_unfold. apply _.
  Qed.
  Program Fixpoint interp_ectx {S} (K : ectx S) : interp_scope S -n> IT -n> IT
    :=
      match K with
      | [] => λne env, idfun
      | Ki::K => λne env, interp_ectx K env ◎ interp_ctx_item Ki env
      end.
  Next Obligation. solve_proper. Defined. (* XXX why can't i qed here? *)

  Lemma interp_ctx_item_fill {S} (Ki : ectx_item S) e env :
    interp_expr (fill_item Ki e) env ≡ interp_ctx_item Ki env (interp_expr e env).
  Proof. destruct Ki; reflexivity. Qed.

  Lemma interp_ectx_fill {S} (K : ectx S) e env :
    interp_expr (fill K e) env ≡ interp_ectx K env (interp_expr e env).
  Proof.
    revert e; induction K as [|Ki K]=>e; first done.
    rewrite IHK. simpl. rewrite interp_ctx_item_fill. done.
  Qed.

  (** Applying renamings and subsitutions to the interpretation of scopes *)
  Equations interp_rens_scope {S S' : scope}
            (E : interp_scope S') (s : rens S S') : interp_scope S :=
    interp_rens_scope (S:=[]) E s := tt : interp_scope [];
    interp_rens_scope (S:=_::_) E s :=
      (interp_var (hd_ren s) E, interp_rens_scope E (tl_ren s)).

  Equations interp_subs_scope {S S' : scope}
            (E : interp_scope S') (s : subs S S') : interp_scope S :=
    interp_subs_scope (S:=[]) E s := tt : interp_scope [];
    interp_subs_scope (S:=_::_) E s :=
      (interp_expr (hd_sub s) E, interp_subs_scope E (tl_sub s)).


  Global Instance interp_rens_scope_ne S S2 n :
    Proper ((dist n) ==> (≡) ==> (dist n)) (@interp_rens_scope S S2).
  Proof.
    intros D D' HE s1 s2 Hs.
    induction S as [|τ' S]; simp interp_rens_scope; auto.
    f_equiv.
    - unfold hd_ren; rewrite Hs. by f_equiv.
    - apply IHS. intros v. unfold tl_ren; by rewrite Hs.
  Qed.
  Global Instance interp_subs_scope_ne S S2 n :
    Proper ((dist n) ==> (≡) ==> (dist n)) (@interp_subs_scope S S2).
  Proof.
    intros D D' HE s1 s2 Hs.
    induction S as [|τ' S]; simp interp_subs_scope; auto.
    f_equiv.
    - unfold hd_sub; by rewrite Hs HE.
    - apply IHS. intros v. unfold tl_sub; by rewrite Hs.
  Qed.
  Global Instance interp_rens_scope_proper S S2 :
    Proper ((≡) ==> (≡) ==> (≡)) (@interp_rens_scope S S2).
  Proof.
    intros D D' HE s1 s2 Hs.
    induction S as [|τ' S]; simp interp_rens_scope; auto.
    f_equiv.
    - unfold hd_ren; rewrite Hs.
      by rewrite HE.
    - apply IHS. intros v. unfold tl_ren; by rewrite Hs.
  Qed.
  Global Instance interp_subs_scope_proper S S2 :
    Proper ((≡) ==> (≡) ==> (≡)) (@interp_subs_scope S S2).
  Proof.
    intros D D' HE s1 s2 Hs.
    induction S as [|τ' S]; simp interp_subs_scope; auto.
    f_equiv.
    - unfold hd_sub; by rewrite Hs HE.
    - apply IHS. intros v. unfold tl_sub; by rewrite Hs.
  Qed.

  (** ** The substituion lemma, for renamings and substitutions *)
  Lemma interp_rens_scope_tl_ren {S S2} x D (r : rens S S2) :
    interp_rens_scope ((x, D) : interp_scope (()::S2)) (tl_ren (rens_lift r))
                    ≡ interp_rens_scope D r.
  Proof.
    induction S as [|τ' S]; simp interp_rens_scope; eauto.
    f_equiv.
    { unfold hd_ren, tl_ren. simp rens_lift interp_var.
      done. }
    { rewrite -IHS. f_equiv. clear.
      intros v. dependent elimination v;
        unfold hd_ren, tl_ren; simp rens_lift; auto. }
  Qed.

  Lemma interp_rens_scope_idren {S} (D : interp_scope S) :
    interp_rens_scope D (@idren S) ≡ D.
  Proof.
    induction S as [|[] S]; simp interp_rens_scope.
    { by destruct D. }
    destruct D as [x D]. simp interp_var. simpl.
    f_equiv.
    trans (interp_rens_scope ((x, D) : interp_scope (()::S)) (tl_ren (rens_lift idren))).
    { f_equiv. intros v. unfold tl_ren.
      reflexivity. }
    rewrite interp_rens_scope_tl_ren.
    apply IHS.
  Qed.

  Lemma interp_expr_ren {S D : scope} (M : expr S) (r : rens S D) :
    ∀ (E : interp_scope D),
      interp_expr (ren_expr M r) E ≡ interp_expr M (interp_rens_scope E r)
  with interp_val_ren {S D : scope} (v : val S) (r : rens S D) :
    ∀ (E : interp_scope D),
      interp_val (ren_val v r) E ≡ interp_val v (interp_rens_scope E r).
  Proof.
    - revert D r. induction M=> D r D2; simpl; simp ren_expr.
      all: try by (simpl; repeat intro; simpl; repeat f_equiv; eauto).
      + (* variable *) revert r.
        induction v=>r.
        * simp interp_var interp_rens_scope. done.
        * simp interp_var interp_rens_scope. simpl.
          apply (IHv (tl_ren r)).
      + (* recursive functions *) simp ren_expr. simpl.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr M)).
        iApply f_equivI. iNext. iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_ren.
        iApply f_equivI.
        simp interp_rens_scope interp_var. simpl.
        rewrite !interp_rens_scope_tl_ren.
        iRewrite "IH".
        done.
    - revert D r. induction v=> D r D2; simpl; simp ren_val; eauto.
      (* recursive functions *)
      simp ren_expr. simpl.
      apply bi.siProp.internal_eq_soundness.
      iLöb as "IH".
      rewrite {2}interp_rec_unfold.
      rewrite {2}(interp_rec_unfold (interp_expr e)).
      iApply f_equivI. iNext. iApply internal_eq_pointwise.
      rewrite /ir_unf. iIntros (x). simpl.
      rewrite interp_expr_ren.
      iApply f_equivI.
      simp interp_rens_scope interp_var. simpl.
      rewrite !interp_rens_scope_tl_ren.
      iRewrite "IH".
      done.
  Qed.

  Lemma interp_subs_scope_tl_sub {S S2} x D (s : subs S S2) :
    interp_subs_scope ((x, D) : interp_scope (()::S2)) (tl_sub (subs_lift s))
                    ≡ interp_subs_scope D s.
  Proof.
    induction S as [|[] S]; simp interp_subs_scope; first done.
    f_equiv.
    { unfold hd_sub, tl_sub. simp subs_lift interp_var.
      unfold expr_lift. rewrite interp_expr_ren. f_equiv.
      trans (interp_rens_scope ((x, D) : interp_scope (()::S2)) (tl_ren (rens_lift idren))).
      { f_equiv. intros v. unfold tl_ren.
        simp rens_lift idren. done. }
      rewrite interp_rens_scope_tl_ren.
      apply interp_rens_scope_idren. }
    { rewrite -IHS. f_equiv. clear.
      intros v. dependent elimination v;
        unfold hd_sub, tl_sub; simp subs_lift; auto. }
  Qed.

  Lemma interp_subs_scope_idsub {S} (env : interp_scope S) :
    interp_subs_scope env idsub ≡ env.
  Proof.
    induction S as [|[] S]; simp interp_subs_scope.
    { by destruct env. }
    destruct env as [x env].
    unfold hd_sub, idsub. simpl.
    simp interp_var. simpl. f_equiv.
    etrans; last first.
    { apply IHS. }
    rewrite -(interp_subs_scope_tl_sub x env idsub).
    repeat f_equiv. intro v. unfold tl_sub, idsub; simpl.
    simp subs_lift. unfold expr_lift. simp ren_expr. done.
  Qed.

  Lemma interp_expr_subst {S D : scope} (M : expr S) (s : subs S D) :
    ∀ (E : interp_scope D),
      interp_expr (subst_expr M s) E ≡ interp_expr M (interp_subs_scope E s)
  with interp_val_subst {S D : scope} (v : val S) (s : subs S D) :
    ∀ (E : interp_scope D),
      interp_val (subst_val v s) E ≡ interp_val v (interp_subs_scope E s).
  Proof.
    - revert D s. induction M=> D r D2; simpl; simp subst_expr.
      all: try by (simpl; repeat intro; simpl; repeat f_equiv; eauto).
      + (* variable *) revert r.
        induction v=>r.
        * simp interp_var interp_rens_scope. done.
        * simp interp_var interp_rens_scope. simpl.
          apply (IHv (tl_sub r)).
      + (* recursive functions *) simpl.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr M)).
        iApply f_equivI. iNext. iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_subst.
        iApply f_equivI.
        simp interp_subs_scope interp_var. simpl.
        rewrite !interp_subs_scope_tl_sub.
        iRewrite "IH".
        done.
    - revert D s. induction v=> D r D2; simpl; simp subst_val; eauto.
      (* recursive functions *)
      simp subst_expr. simpl.
      apply bi.siProp.internal_eq_soundness.
      iLöb as "IH".
      rewrite {2}interp_rec_unfold.
      rewrite {2}(interp_rec_unfold (interp_expr e)).
      iApply f_equivI. iNext. iApply internal_eq_pointwise.
      rewrite /ir_unf. iIntros (x). simpl.
      rewrite interp_expr_subst.
      iApply f_equivI.
      simp interp_subs_scope interp_var. simpl.
      rewrite !interp_subs_scope_tl_sub.
      iRewrite "IH".
      done.
  Qed.

  (** ** Interpretation commutes with ticks and INPUT *)
  Lemma interp_ectx_item_INPUT {S} (Ki : ectx_item S) f env :
    interp_ctx_item Ki env (INPUT f) ≡ INPUT (interp_ctx_item Ki env ◎ f).
  Proof.
    destruct Ki; cbn-[IF APP' INPUT Tick Tick_n get_nat2].
    Transparent INPUT.
    - rewrite !APP_APP'_ITV.
      rewrite APP_Vis. unfold INPUT. simpl. repeat f_equiv.
      intro.
      cbn-[APP]. rewrite laterO_map_Next. simpl.
      f_equiv.
      by rewrite -APP_APP'_ITV.
    - rewrite APP'_Vis_r. unfold INPUT. simpl. repeat f_equiv.
      intro. simpl. rewrite laterO_map_Next. reflexivity.
    - rewrite NATOP_ITV_Vis_l/=.
      repeat f_equiv. intro x. simpl. reflexivity.
    - rewrite NATOP_Vis_r/=.
      repeat f_equiv. intro x. simpl. reflexivity.
    - rewrite IF_Vis/=. repeat f_equiv.
      by intro.
    Opaque INPUT.
  Qed.

  Lemma interp_ectx_INPUT {S} (K : ectx S) f env :
    interp_ectx K env (INPUT f) ≡ INPUT (interp_ectx K env ◎ f).
  Proof.
    revert f. induction K as [|Ki K]=>f.
    - simpl. f_equiv. intro; reflexivity.
    - simpl. rewrite interp_ectx_item_INPUT.
      rewrite IHK. f_equiv. intro. reflexivity.
  Qed.

  Lemma interp_ectx_item_tick {S} (Ki : ectx_item S) env t n :
    interp_ctx_item Ki env (Tick_n n t) ≡ Tick_n n (interp_ctx_item Ki env t).
  Proof.
    destruct Ki; cbn-[Tick_n IF].
    - rewrite APP_APP'_ITV. rewrite APP_Tick_n.
      rewrite -APP_APP'_ITV. done.
    - rewrite APP'_Tick_r_n. done.
    - rewrite NATOP_ITV_Tick_n_l//.
    - rewrite NATOP_Tick_n_r//.
    - rewrite IF_Tick_n//.
  Qed.

  Lemma interp_ectx_tick {S} (K : ectx S) env t n :
    interp_ectx K env (Tick_n n t) ≡ Tick_n n (interp_ectx K env t).
  Proof.
    revert t. induction K as [|Ki K]=>t; first done.
    cbn-[Tick_n].
    trans (interp_ectx K env (Tick_n n $ interp_ctx_item Ki env t)).
    { f_equiv. apply interp_ectx_item_tick. }
    by rewrite IHK.
  Qed.

  (** ** Finally, preservation of reductions *)
  Lemma interp_expr_head_step {S} env (e : expr S) e' σ σ' n :
    head_step e σ e' σ' (n,0) →
    interp_expr e env ≡ Tick_n n $ interp_expr e' env.
  Proof.
    inversion 1; cbn-[IF APP' INPUT Tick get_nat2].
    - (*fun->val*)
      reflexivity.
    - (* app lemma *)
      rewrite APP_APP'_ITV.
      trans (APP (Fun (Next (ir_unf (interp_expr e1) env))) (Next $ interp_val v2 env)).
      { repeat f_equiv. apply interp_rec_unfold. }
      rewrite APP_Fun. simpl. rewrite Tick_eq. do 2 f_equiv.
      simplify_eq.
      rewrite interp_expr_subst. f_equiv.
      simp interp_subs_scope. unfold hd_sub, tl_sub. simp conssub.
      simpl. repeat f_equiv.
      generalize (Val (RecV e1)).
      generalize (Val v2).
      clear.
      intros e1 e2.
      trans (interp_subs_scope env idsub); last first.
      {  f_equiv. intro v. simp conssub. done. }
      symmetry.
      apply interp_subs_scope_idsub.
    - (* the natop stuff *)
      simplify_eq.
      destruct v1,v2; try naive_solver. simpl in *.
      rewrite NATOP_Nat.
      destruct op; simplify_eq/=; done.
    - by rewrite IF_True.
    - rewrite IF_False; eauto. lia.
  Qed.

  Lemma interp_expr_fill_no_reify {S} K env (e e' : expr S) σ σ' n :
    head_step e σ e' σ' (n,0) →
    interp_expr (fill K e) env ≡ Tick_n n $ interp_expr (fill K e') env.
  Proof.
    intros He.
    trans (interp_ectx K env (interp_expr e env)).
    { apply interp_ectx_fill. }
    trans (interp_ectx K env (Tick_n n (interp_expr e' env))).
    {  f_equiv. apply (interp_expr_head_step env) in He. apply He. }
    trans (Tick_n n $ interp_ectx K env (interp_expr e' env)); last first.
    { f_equiv. symmetry. apply interp_ectx_fill. }
    apply interp_ectx_tick.
  Qed.

  Lemma interp_expr_fill_yes_reify {S} K env (e e' : expr S)
    (σ σ' : stateO) (σr : gState_rest sR_idx rs ♯ IT) n :
    head_step e σ e' σ' (n,1) →
    reify rs (interp_expr (fill K e) env)  (gState_recomp σr (subR_conv_state σ))
      ≡ (gState_recomp σr (subR_conv_state σ'), Tick_n n $ interp_expr (fill K e') env).
  Proof.
    inversion 1; simplify_eq.
    trans (reify rs (interp_ectx K env (interp_expr Input env))
             (gState_recomp σr (subR_conv_state σ))).
    { f_equiv. by rewrite interp_ectx_fill. }
    simpl.
    trans (reify rs (INPUT (interp_ectx K env ◎ Nat)) (gState_recomp σr (subR_conv_state σ))).
    { f_equiv; eauto.
      by rewrite interp_ectx_INPUT. }
    rewrite reify_vis_eq //; last first.
    { rewrite subReifier_reify/=//.
      rewrite H5. done. }
    repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
    rewrite interp_ectx_fill.
    rewrite ofe_iso_21.
    done.
  Qed.

  Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m env :
    prim_step e1 σ1 e2 σ2 (n,m) →
    ssteps rs (interp_expr e1 env) (gState_recomp σr (subR_conv_state σ1))
              (interp_expr e2 env) (gState_recomp σr (subR_conv_state σ2)) n.
  Proof.
    Opaque gState_decomp gState_recomp.
    inversion 1; simplify_eq/=.
    destruct (head_step_io_01 _ _ _ _ _ _ H2); subst.
    - assert (σ1 = σ2) as ->.
      { eapply head_step_no_io; eauto. }
      eapply (interp_expr_fill_no_reify K) in H2.
      rewrite H2. eapply ssteps_tick_n.
    - inversion H2;subst. eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
      rewrite interp_ectx_fill interp_ectx_INPUT.
      change 1 with (1+0). econstructor; last first.
      { apply ssteps_zero; reflexivity. }
      eapply sstep_reify.
      { Transparent INPUT. unfold INPUT. simpl.
        f_equiv. reflexivity. }
      simpl in H2.
      rewrite -H2.
      repeat f_equiv; eauto.
      rewrite interp_ectx_fill interp_ectx_INPUT.
      eauto.
  Qed.

End interp.

