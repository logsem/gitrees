From gitrees Require Import gitree lang_generic.
From gitrees.effects Require Export prng.
From gitrees.examples.prng_lang Require Import lang.

Require Import Binding.Lib Binding.Set.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers NotCtxDep sz).
  Context {subR : subReifier reify_prng rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R} `{!SubOfe locO R} `{!SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Global Instance denot_cont_ne (κ : IT -n> IT) :
    NonExpansive (λ x : IT, Tau (laterO_map κ (Next x))).
  Proof.
    solve_proper.
  Qed.

  (** Interpreting individual operators *)
  (* TODO: these interpretation might be unsound.
     Problems with evaluation order.
     Problems with "going under Tau/Vis constructor"
  *)
  Program Definition interp_new {A} : A -n> IT :=
    λne env, PRNG_NEW Ret.
  Program Definition interp_del {A} (l : A -n> IT) : A -n> IT :=
    λne env, get_ret PRNG_DEL (l env).
  Program Definition interp_rand {A} (l : A -n> IT) : A -n> IT :=
    λne env, get_ret (PRNG_GEN) (l env).

  Program Definition SEED_FUN : IT -n> IT -n> IT :=
    λne s, get_ret (λne vLoc : locO, get_ret (PRNG_SEED vLoc) s).
  Solve All Obligations with solve_proper_please.
  Program Definition SEED_IT : IT := λit s l, SEED_FUN s l.
  Solve All Obligations with solve_proper_please.

  (* NOTE:
     1. The interpretation should be a homomorphism in both arguments.
     2. The PRNG location should be evaluated first.

     APP is left-associative.
  *)
  Program Definition interp_seed {A} (l s : A -n> IT) : A -n> IT :=
    λne env, SEED_IT ⊙ (s env) ⊙ (l env).
  Solve All Obligations with solve_proper_please.

  Lemma seed_it_app_ret_ret (l : locO) (s : natO) :
    SEED_IT ⊙ (Ret s) ⊙ (Ret l) ≡ Tick_n 2 $ PRNG_SEED l s.
  Proof.
    rewrite (APP'_Ret_r (SEED_IT ⊙ (Ret s))).
    rewrite (APP'_Ret_r SEED_IT).
    rewrite APP_Fun.
    rewrite APP_Tick.
    rewrite APP_Fun.
    simpl.
    f_equiv.
    rewrite get_ret_ret.
    simpl.
    rewrite get_ret_ret.
    simpl.
    done.
  Qed.

  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_natop.

  Opaque laterO_map.
  Program Definition interp_rec_pre {S : Set} (body : interp_scope (inc (inc S)) -n> IT)
    : laterO (interp_scope S -n> IT) -n> interp_scope S -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : interp_scope S -n> IT) (a : IT),
                      body (extend_scope (extend_scope env (self env)) a)) self.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros ??????? H.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; [done | apply H | done].
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv.
    apply laterO_map_ne.
    intros ??; simpl; f_equiv;
    intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    by do 2 f_equiv.
  Qed.

  Program Definition interp_rec {S : Set}
    (body : interp_scope (inc (inc S)) -n> IT) :
    interp_scope S -n> IT :=
    mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set}
    (body : interp_scope (inc (inc S)) -n> IT) env : IT -n> IT :=
    λne a, body (extend_scope
                   (extend_scope env (interp_rec body env))
                   a).
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv. intros [| [| y']]; simpl; solve_proper.
  Qed.

  Lemma interp_rec_unfold {S : Set} (body : interp_scope (inc (inc S)) -n> IT) env :
    interp_rec body env ≡ Fun $ Next $ ir_unf body env.
  Proof.
    trans (interp_rec_pre body (Next (interp_rec body)) env).
    { f_equiv. rewrite /interp_rec. apply mmuu_unfold. }
    simpl. rewrite laterO_map_Next. repeat f_equiv.
    simpl. unfold ir_unf. intro. simpl. reflexivity.
  Qed.

  Program Definition interp_app {A} (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, APP' (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_app_ne A : NonExpansive2 (@interp_app A).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_app.

  Program Definition interp_if {A} (t0 t1 t2 : A -n> IT) : A -n> IT :=
    λne env, IF_nat.IF (t0 env) (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  Program Definition interp_unit {A} : A -n> IT :=
    λne env, Ret ().
  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Ret n.
  Program Definition interp_loc (l : loc) {A} : A -n> IT :=
    λne env, Ret l.

  Program Definition interp_applk {A}
    (K : A -n> (IT -n> IT))
    (q : A -n> IT)
    : A -n> (IT -n> IT) :=
    λne env t, interp_app (λne env, K env t) q env.
  Solve All Obligations with solve_proper.

  Program Definition interp_apprk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_app q (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoprk {A} (op : nat_op)
    (q : A -n> IT)
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_natop op q (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoplk {A} (op : nat_op)
    (K : A -n> (IT -n> IT))
    (q : A -n> IT) : A -n> (IT -n> IT) :=
    λne env t, interp_natop op (λne env, K env t) q env.
  Solve All Obligations with solve_proper.

  Program Definition interp_ifk {A} (K : A -n> (IT -n> IT)) (q : A -n> IT)
    (p : A -n> IT) : A -n> (IT -n> IT) :=
    λne env t, interp_if (λne env, K env t) q p env.
  Solve All Obligations with solve_proper.


  Program Definition interp_delk {A} (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_del (λne env, K env t) env.
  Program Definition interp_seedkl {A} (K : A -n> (IT -n> IT)) (eSeed : A -n> IT) : A -n> (IT -n> IT) :=
    λne env t, interp_seed (λne env, K env t) eSeed env.
  Program Definition interp_seedks {A} (vprng : A -n> IT) (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_seed vprng (λne env, K env t) env.
  Program Definition interp_randk {A} (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_rand (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.


  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | UnitV => interp_unit
    | LitV n => interp_nat n
    | LitPrng l => interp_loc l
    | RecV e => interp_rec (interp_expr e)
    end
  with interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
         match e with
         | Val v => interp_val v
         | Var x => interp_var x
         | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
         | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
         | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
         | NewPrng => interp_new
         | DelPrng e => interp_del (interp_expr e)
         | Seed el es => interp_seed (interp_expr el) (interp_expr es)
         | Rand e => interp_rand (interp_expr e)
         end.
  Fixpoint interp_ectx {S} (K : ectx S) : interp_scope S -n> (IT -n> IT) :=
    match K with
    | EmptyK => λne env, idfun
    | AppRK e1 K => interp_apprk (interp_expr e1) (interp_ectx K)
    | AppLK K v2 => interp_applk (interp_ectx K) (interp_val v2)
    | NatOpRK op e1 K => interp_natoprk op (interp_expr e1) (interp_ectx K)
    | NatOpLK op K v2 => interp_natoplk op (interp_ectx K) (interp_val v2)
    | IfK K e1 e2 => interp_ifk (interp_ectx K) (interp_expr e1) (interp_expr e2)
    | DelPrngK K => interp_delk (interp_ectx K)
    | SeedKl K es => interp_seedkl (interp_ectx K) (interp_expr es)
    | SeedKs vl K => interp_seedks (interp_val vl) (interp_ectx K)
    | RandK K => interp_randk (interp_ectx K)
    end.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

  Global Instance interp_val_asval {S} {D : interp_scope S} (v : val S)
    : AsVal (interp_val v D).
  Proof.
    destruct v; simpl.
    - apply _.
    - apply _.
    - apply _.
    - rewrite interp_rec_unfold. apply _.
  Qed.

  Global Instance ArrEquiv {A B : Set} : Equiv (A [→] B) :=
    fun f g => ∀ x, f x = g x.

  Global Instance ArrDist {A B : Set} `{Dist B} : Dist (A [→] B) :=
    fun n => fun f g => ∀ x, f x ≡{n}≡ g x.

  Global Instance ren_scope_proper {S S'} :
    Proper ((≡) ==> (≡) ==> (≡)) (@ren_scope F _ CR S S').
  Proof.
    intros D D' HE s1 s2 Hs.
    intros x; simpl.
    f_equiv.
    - apply Hs.
    - apply HE.
 Qed.

  Lemma interp_expr_ren {S S'} env
    (δ : S [→] S') (e : expr S) :
    interp_expr (fmap δ e) env ≡ interp_expr e (ren_scope δ env)
  with interp_val_ren {S S'} env
         (δ : S [→] S') (e : val S) :
    interp_val (fmap δ e) env ≡ interp_val e (ren_scope δ env)
  with interp_ectx_ren {S S'} env
         (δ : S [→] S') (e : ectx S) :
    interp_ectx (fmap δ e) env ≡ interp_ectx e (ren_scope δ env).
  Proof.
    - destruct e; simpl.
      + by apply interp_val_ren.
      + reflexivity.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
    - destruct e; simpl.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + clear -interp_expr_ren.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 1 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_ren.
        iApply f_equivI.
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done.
        * by iRewrite - "IH".
        * done.
    - destruct e; simpl; intros ?; simpl.
      + reflexivity.
      + repeat f_equiv; by apply interp_ectx_ren.
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_ectx_ren].
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_val_ren].
      + repeat f_equiv; by apply interp_ectx_ren.
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_expr_ren | by apply interp_expr_ren].
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_val_ren].
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_ectx_ren].
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_ectx_ren].
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_val_ren].
  Qed.

  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : ectx S):
    interp_expr (fill K e) env ≡ (interp_ectx K) env ((interp_expr e) env).
  Proof.
    revert env.
    induction K; simpl; intros env; first reflexivity; try (by rewrite IHK).
  Qed.

  Program Definition sub_scope {S S'} (δ : S [⇒] S') (env : interp_scope S')
    : interp_scope S := λne x, interp_expr (δ x) env.

  Global Instance SubEquiv {A B : Set} : Equiv (A [⇒] B) := fun f g => ∀ x, f x = g x.

  Global Instance sub_scope_proper {S S'} :
    Proper ((≡) ==> (≡) ==> (≡)) (@sub_scope S S').
  Proof.
    intros D D' HE s1 s2 Hs.
    intros x; simpl.
    f_equiv.
    - f_equiv.
      apply HE.
    - apply Hs.
 Qed.

  Lemma interp_expr_subst {S S'} (env : interp_scope S')
    (δ : S [⇒] S') e :
    interp_expr (bind δ e) env ≡ interp_expr e (sub_scope δ env)
  with interp_val_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') e :
    interp_val (bind δ e) env ≡ interp_val e (sub_scope δ env)
  with interp_ectx_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') e :
    interp_ectx (bind δ e) env ≡ interp_ectx e (sub_scope δ env).
  Proof.
    - destruct e; simpl.
      + by apply interp_val_subst.
      + term_simpl.
        reflexivity.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
      + f_equiv.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
    - destruct e; simpl.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + clear -interp_expr_subst.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 1 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_subst.
        iApply f_equivI.
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done.
        * by iRewrite - "IH".
        * do 2 rewrite interp_expr_ren.
          iApply f_equivI.
          iApply internal_eq_pointwise.
          iIntros (z).
          done.
    - destruct e; simpl; intros ?; simpl.
      + reflexivity.
      + repeat f_equiv; by apply interp_ectx_subst.
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_ectx_subst].
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_val_subst].
      + repeat f_equiv; by apply interp_ectx_subst.
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_expr_subst | by apply interp_expr_subst].
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_val_subst].
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_ectx_subst].
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_ectx_subst].
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_val_subst].
  Qed.

  (** ** Interpretation of evaluation contexts induces homomorphism *)

  #[local] Instance interp_ectx_hom_emp {S} env :
    IT_hom (interp_ectx (EmptyK : ectx S) env).
  Proof.
    simple refine (IT_HOM _ _ _ _ _); intros; auto.
    simpl. fold (@idfun IT). f_equiv. intro. simpl.
    by rewrite laterO_map_id.
  Qed.


  #[local] Instance interp_ectx_hom_del {S} (K : ectx S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (DelPrngK K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis.
      f_equiv. intro. simpl. rewrite -laterO_map_compose.
      do 2 f_equiv. by intro.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_ectx_hom_rand {S} (K : ectx S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (RandK K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis.
      f_equiv. intro. simpl. rewrite -laterO_map_compose.
      do 2 f_equiv. by intro.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_ectx_hom_seedkl {S} (K : ectx S) (eSeed : expr S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (SeedKl K eSeed) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis.
      f_equiv. intro. simpl. rewrite -laterO_map_compose.
      do 2 f_equiv. by intro.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_ectx_hom_seedks {S} (vprng : val S) (K : ectx S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (SeedKs vprng K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite !hom_tick.
      erewrite APP'_Tick_l; first done.
      by apply interp_val_asval.
    - rewrite hom_vis.
      rewrite APP'_Vis_r.
      rewrite APP'_Vis_l.
      f_equiv.
      intros ?. simpl. by rewrite -laterO_map_compose.
    - rewrite hom_err.
      rewrite APP'_Err_r.
      rewrite APP'_Err_l.
      done.
  Qed.


  #[local] Instance interp_ectx_hom_if {S}
    (K : ectx S) (e1 e2 : expr S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (IfK K e1 e2) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -IF_nat.IF_Tick. f_equiv. apply hom_tick.
    - assert ((interp_ectx K env (Vis op i ko)) ≡
        (Vis op i (laterO_map (λne y, interp_ectx K env y) ◎ ko))).
      { by rewrite hom_vis. }
      trans (IF_nat.IF (Vis op i (laterO_map (λne y : IT, interp_ectx K env y) ◎ ko))
               (interp_expr e1 env) (interp_expr e2 env)).
      { f_equiv. by rewrite hom_vis. }
      rewrite IF_nat.IF_Vis. f_equiv. simpl.
      intro. simpl. by rewrite -laterO_map_compose.
    - trans (IF_nat.IF (Err e) (interp_expr e1 env) (interp_expr e2 env)).
      { repeat f_equiv. apply hom_err. }
      apply IF_nat.IF_Err.
  Qed.

  #[local] Instance interp_ectx_hom_appr {S} (K : ectx S)
    (e : expr S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (AppRK e K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_ectx_hom_appl {S} (K : ectx S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (AppLK K v) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -APP'_Tick_l. f_equiv. apply hom_tick.
    - trans (APP' (Vis op i (laterO_map (interp_ectx K env) ◎ ko))
               (interp_val v env)).
      + f_equiv. rewrite hom_vis. do 3 f_equiv. by intro.
      + rewrite APP'_Vis_l. f_equiv. intro x. simpl.
        by rewrite -laterO_map_compose.
    - trans (APP' (Err e) (interp_val v env)).
      { f_equiv. apply hom_err. }
      apply APP'_Err_l, interp_val_asval.
  Qed.

  #[local] Instance interp_ectx_hom_natopr {S} (K : ectx S)
    (e : expr S) op env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (NatOpRK op e K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_ectx_hom_natopl {S} (K : ectx S)
    (v : val S) op (env : interp_scope S) :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (NatOpLK op K v) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -NATOP_ITV_Tick_l. f_equiv. apply hom_tick.
    - trans (NATOP (do_natop op)
               (Vis op0 i (laterO_map (interp_ectx K env) ◎ ko))
               (interp_val v env)).
      { f_equiv. rewrite hom_vis. f_equiv. by intro. }
      rewrite NATOP_ITV_Vis_l. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - trans (NATOP (do_natop op) (Err e) (interp_val v env)).
      + f_equiv. apply hom_err.
      + by apply NATOP_Err_l, interp_val_asval.
  Qed.

  #[global] Instance interp_ectx_hom {S} (K : ectx S) env :
    IT_hom (interp_ectx K env).
  Proof.
    induction K; apply _.
  Qed.

  (** ** Finally, preservation of reductions *)
  Lemma interp_expr_head_step {S : Set} (env : interp_scope S) (e : expr S) e' σ σ' n :
    head_step e σ e' σ' (n, 0) →
    interp_expr e env ≡ Tick_n n $ interp_expr e' env.
  Proof.
    inversion 1; cbn-[IF_nat.IF APP' Tick].
    - (* app lemma *)
      subst.
      erewrite APP_APP'_ITV; last apply _.
      trans (APP (Fun (Next (ir_unf (interp_expr e1) env))) (Next $ interp_val v2 env)).
      { repeat f_equiv. apply interp_rec_unfold. }
      rewrite APP_Fun. simpl. rewrite Tick_eq. do 2 f_equiv.
      simplify_eq.
      rewrite !interp_expr_subst.
      f_equiv.
      intros [| [| x]]; simpl; [| reflexivity | reflexivity].
      rewrite interp_val_ren.
      f_equiv.
      intros ?; simpl; reflexivity.
    - rewrite IF_nat.IF_True; last lia.
      reflexivity.
    - rewrite IF_nat.IF_False; last lia.
      reflexivity.
    - (* the natop stuff *)
      simplify_eq.
      destruct v1,v2; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
  Qed.

  Lemma interp_expr_fill_no_reify {S} K (env : interp_scope S) (e e' : expr S) σ σ' n :
    head_step e σ e' σ' (n, 0) →
    interp_expr (fill K e) env
      ≡
      Tick_n n $ interp_expr (fill K e') env.
  Proof.
    intros He.
    rewrite !interp_comp.
    erewrite <-hom_tick_n.
    - apply (interp_expr_head_step env) in He.
      rewrite He.
      reflexivity.
    - apply _.
  Qed.

  Opaque PRNG_NEW PRNG_DEL PRNG_SEED PRNG_GEN.
  Opaque extend_scope.
  Opaque Ret.

  (* from [prng.v] *)
  Notation opid_new := (inl ()).
  Notation opid_del := (inr opid_new).
  Notation opid_gen := (inr opid_del).
  Notation opid_seed := (inr opid_gen).

  (* TODO: streamline the repetitive proof script *)
  Lemma interp_expr_fill_yes_reify {S} K env (e e' : expr S)
    (σ σ' : stateO) (σr : gState_rest sR_idx rs ♯ IT) n :
    head_step e σ e' σ' (n, 1) →
    reify (gReifiers_sReifier rs)
      (interp_expr (fill K e) env) (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K e') env, []).
  Proof.
    intros Hst.
    trans (reify (gReifiers_sReifier rs) (interp_ectx K env (interp_expr e env))
             (gState_recomp σr (sR_state σ))).
    { f_equiv. by rewrite interp_comp. }
    inversion Hst; simplify_eq; cbn-[gState_recomp].
    - trans (reify (gReifiers_sReifier rs) (PRNG_NEW (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv; eauto.
        rewrite hom_NEW.
        do 2 f_equiv. by intro.
      }
      rewrite reify_vis_eq_ctx_indep //; first last.
      {
        epose proof (@subReifier_reify sz NotCtxDep reify_prng rs _ IT _ opid_new () l σ σ' σr []) as H.
        simpl in H.
        simpl.
        erewrite <-H; last first.
        - unfold state_new in H4.
          inversion H4.
          reflexivity.
        - f_equiv;
          solve_proper.
      }
      repeat f_equiv; last done. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      rewrite ofe_iso_21.
      simpl.
      reflexivity.
    - trans (reify (gReifiers_sReifier rs) (PRNG_DEL_k l (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv.
        rewrite get_ret_ret.
        rewrite hom_DEL_k.
        f_equiv; f_equiv.
        by intro.
      }
      rewrite reify_vis_eq_ctx_indep //; last first.
      {
        epose proof (@subReifier_reify sz NotCtxDep reify_prng rs _ IT _ opid_del l () σ σ' σr []) as H.
        simpl in H.
        rewrite H4 in H.
        simpl.
        erewrite <-H; last reflexivity.
        f_equiv.
      }
      repeat f_equiv; last done. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      by rewrite ofe_iso_21.
    - trans (reify (gReifiers_sReifier rs) (PRNG_GEN_k l (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv.
        rewrite get_ret_ret.
        rewrite hom_GEN_k.
        f_equiv; f_equiv.
        by intro.
      }
      rewrite reify_vis_eq_ctx_indep //; last first.
      {
        epose proof (@subReifier_reify sz NotCtxDep reify_prng rs _ IT _ opid_gen l n0 σ σ' σr []) as H.
        simpl in H.
        rewrite H4 in H.
        simpl.
        erewrite <-H; last reflexivity.
        f_equiv.
      }
      repeat f_equiv; last done. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      by rewrite ofe_iso_21.
    - trans (reify (gReifiers_sReifier rs) (Tick_n 2 $ PRNG_SEED_k l n0 (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        f_equiv; last done; f_equiv.
        rewrite seed_it_app_ret_ret.
        rewrite !hom_tick.
        rewrite hom_SEED_k.
        simpl; do 4 f_equiv.
        intro; simpl; done.
      }
      trans (reify (gReifiers_sReifier rs)
      (PRNG_SEED_k l n0 (Tick ◎ Tick ◎ interp_ectx K env ◎ Ret))
      (gState_recomp σr (sR_state σ))).
      {
        do 2 f_equiv.
        (* FIXME: maybe this interpretation of [Seed] does not work ?? *)
        admit.
      }
      rewrite reify_vis_eq_ctx_indep //; last first.
      {
        epose proof (@subReifier_reify sz NotCtxDep reify_prng rs _ IT _ opid_seed (l,n0) () σ σ' σr []) as H.
        simpl in H.
        rewrite H4 in H.
        simpl.
        rewrite <-H; last reflexivity.
        f_equiv; solve_proper.
      }
      repeat f_equiv; last done. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      by rewrite ofe_iso_21.
  Admitted.

  Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) :
    prim_step e1 σ1 e2 σ2 (n,m) →
    external_steps (gReifiers_sReifier rs)
              (interp_expr e1 env) (gState_recomp σr (sR_state σ1))
              (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) [] n.
  Proof.
    Opaque gState_decomp gState_recomp.
    inversion 1; simplify_eq/=.
    destruct (head_step_prng_01 _ _ _ _ _ _ H2); subst.
    - assert (σ1 = σ2) as ->.
      { eapply head_step_pure; eauto. }
      unshelve eapply (interp_expr_fill_no_reify K) in H2; first apply env.
      rewrite H2.
      rewrite interp_comp.
      eapply external_steps_tick_n.
    - inversion H2; subst.
      + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
        rewrite interp_comp.
        rewrite hom_NEW.
        change 1 with (Nat.add 1 0). econstructor; last first.
        { constructor; reflexivity. }
        2:{ rewrite app_nil_r; reflexivity. }
        eapply external_step_reify.
        { Transparent PRNG_NEW. unfold PRNG_NEW. simpl.
          f_equiv. reflexivity. }
        simpl in H2.
        rewrite -H2.
        repeat f_equiv; eauto.
        rewrite interp_comp hom_NEW.
        eauto.
      + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
        rewrite interp_comp. simpl.
        rewrite get_ret_ret.
        rewrite hom_DEL_k.
        change 1 with (Nat.add 1 0). econstructor; last first.
        { constructor; reflexivity. }
        2:{ rewrite app_nil_r; reflexivity. }
        eapply external_step_reify.
        { Transparent PRNG_DEL_k. unfold PRNG_DEL_k. simpl.
          f_equiv. reflexivity. }
        simpl in H2.
        rewrite -H2.
        repeat f_equiv; eauto.
        Opaque PRNG_DEL_k.
        rewrite interp_comp /= get_ret_ret hom_DEL_k.
        eauto.
      + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
        rewrite interp_comp. simpl.
        rewrite get_ret_ret.
        rewrite hom_GEN_k.
        change 1 with (Nat.add 1 0). econstructor; last first.
        { constructor; reflexivity. }
        2:{ rewrite app_nil_r; reflexivity. }
        eapply external_step_reify.
        { Transparent PRNG_GEN_k. unfold PRNG_GEN_k. simpl.
          f_equiv. reflexivity. }
        simpl in H2.
        rewrite -H2.
        repeat f_equiv; eauto.
        Opaque PRNG_GEN_k.
        rewrite interp_comp /= get_ret_ret hom_GEN_k.
        eauto.
      + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
        rewrite interp_comp. simpl.
        rewrite seed_it_app_ret_ret; rewrite !Tick_n_S Tick_n_O.
    Admitted.
End interp.
#[global] Opaque PRNG_NEW PRNG_DEL_k PRNG_GEN_k PRNG_SEED_k.
