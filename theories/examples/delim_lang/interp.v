(** Interpretation of delim_lang into gitrees *)
From gitrees Require Import gitree lang_generic.
From gitrees.effects Require Import delim.
From gitrees.examples.delim_lang Require Import lang.
From iris.algebra Require Import list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.

Require Import Binding.Lib Binding.Set.

Program Definition DelimLangGitreeGS {R} `{!Cofe R}
  {a : is_ctx_dep} {n} (rs : gReifiers a n)
  (Σ : gFunctors)
  (H1 : invGS Σ) (H2 : stateG rs R Σ)
  : gitreeGS_gen rs R Σ :=
  GitreeG rs R Σ H1 H2
    (λ _ σ, @state_interp _ _ rs R _ _ H2 σ)
    (λ _, True%I)
    (λ _, True%I)
    _
    (λ x, x)
    _
    _
    _.
Next Obligation.
  intros; simpl.
  iIntros "?". by iModIntro.
Qed.
Next Obligation.
  intros; simpl. iSplit; iIntros "H".
  - by iFrame "H".
  - by iDestruct "H" as "(_ & ?)".
Qed.

Import IF_nat.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
  Context {subR : subReifier reify_delim rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation state := (stateF ♯ IT).
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Global Instance denot_cont_ne (κ : later IT -n> later IT) :
    NonExpansive (λ x : IT, Tau (κ (Next x))).
  Proof. solve_proper. Defined.

  (** * Interpreting individual operators *)

  (** ** RESET *)

  Program Definition interp_reset {S} (e : S -n> IT) : S -n> IT :=
    λne env, RESET (Next $ e env).
  Solve All Obligations with solve_proper.

  (** ** SHIFT *)

  Program Definition interp_shift {S} (e : @interp_scope F R _ (inc S) -n> IT) :
    interp_scope S -n> IT :=
    λne env, SHIFT (λne (k : laterO IT -n> laterO IT),
                      Next (e (extend_scope env (λit x, Tau (k (Next x)))))).
  Next Obligation. intros; apply denot_cont_ne. Defined.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros [| a]; simpl; last solve_proper.
    repeat f_equiv. solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros [| a]; simpl; last solve_proper.
    repeat f_equiv.
  Qed.

  (** ** NATOP *)
  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_natop.
  
  (** ** REC *)

  Opaque laterO_map.
  Program Definition interp_rec_pre {S : Set} (body : interp_scope (inc (inc S)) -n> IT)
    : laterO (interp_scope S -n> IT) -n> interp_scope S -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : interp_scope S -n> IT) (a : IT),
                      body (extend_scope (extend_scope env (self env)) a)) self.
  Next Obligation.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; done.
  Qed.
  Next Obligation.
    intros.
    intros ???.
    f_equiv.
    apply laterO_map_ne.
    intros ??; simpl; f_equiv;
    intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    intros ????; simpl.
    f_equiv; f_equiv.
    done.
  Qed.

  Program Definition interp_rec {S : Set}
    (body : interp_scope (inc (inc S)) -n> IT) : interp_scope S -n> IT :=
    mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set}
    (body : interp_scope (inc (inc S)) -n> IT) env : IT -n> IT :=
    λne a, body (extend_scope
                   (extend_scope env (interp_rec body env)) a).
  Next Obligation.
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

  (** ** APP *)
  Program Definition interp_app {A} (t1 t2 : A -n> IT) : A -n> IT :=
    λne env,
      LET (t1 env) $ λne f,
      LET (t2 env) $ λne x,
      APP' f x.
  Solve All Obligations with solve_proper_please.

  Global Instance interp_app_ne A : NonExpansive2 (@interp_app A).
  Proof.
    solve_proper_prepare.
    f_equiv.
    - by f_equiv.
    - intro; simpl.
      by do 2 f_equiv.
  Qed.
  Typeclasses Opaque interp_app.

  (** ** APP_CONT *)

  Program Definition interp_app_cont {A} (k e : A -n> IT) : A -n> IT :=
    λne env, get_val (λne x, get_fun
                               (λne (f : laterO (IT -n> IT)),
                                  APP_CONT (Next x) f)
                               (k env))
                     (e env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_app_cont_ne A : NonExpansive2 (@interp_app_cont A).
  Proof.
    intros n??????. rewrite /interp_app_cont. intro. simpl.
    repeat f_equiv; last done. intro. simpl. by repeat f_equiv.
  Qed.
  (* Typeclasses Opaque interp_app_cont. *)

  (** ** IF *)
  Program Definition interp_if {A} (t0 t1 t2 : A -n> IT) : A -n> IT :=
    λne env, IF (t0 env) (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  (** ** NAT *)
  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Ret n.

  (** ** CONT *)
  Program Definition interp_cont_val {S} (K : S -n> (IT -n> IT)) : S -n> IT :=
    λne env, (λit x, Tick $ 𝒫 (K env x)).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_ifk {A} (e1 e2 : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> (IT -n> IT) :=
  λne env b, (K env) $ interp_if (λne env, b) e1 e2 env.
  Solve All Obligations with solve_proper.

  Program Definition interp_apprk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app q (λne env, t) env.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    do 2 f_equiv.
    intro; simpl.
    by f_equiv.
  Qed.
  Next Obligation.
    intros ?? K n x y H a; simpl.
    rewrite (LET_NonExp n (q x) (q y) _); last reflexivity;
      last solve_proper.
    f_equiv; first solve_proper.
    f_equiv. intros ?; simpl.
    reflexivity.
  Qed.

  Program Definition interp_applk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app (λne env, t) q env.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros ?? K n x y H a; simpl.
    f_equiv; first solve_proper.
    f_equiv. intros ?; simpl.
    f_equiv.
    solve_proper.
  Qed.

  Program Definition interp_app_contrk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app_cont q (λne env, t) env.
  Next Obligation. intros A q K t n ????. done. Qed.
  Next Obligation.
    intros A q K env n ???. simpl. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros A q K n ???. intro. simpl. f_equiv.
    - by f_equiv.
    - f_equiv. f_equiv. intro. simpl. by repeat f_equiv.
  Qed.

  Program Definition interp_app_contlk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app_cont (λne env, t) q env.
  Next Obligation. intros A q K t n ????. done. Qed.
  Next Obligation.
    intros A q K env n ???. simpl. repeat f_equiv.
    intro. simpl. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros A q K n ???. intro. simpl. f_equiv.
    - by f_equiv.
    - f_equiv; last by f_equiv. f_equiv.  intro. simpl. repeat f_equiv.
  Qed.

  Program Definition interp_natoprk {A} (op : nat_op) (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_natop op q (λne env, t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoplk {A} (op : nat_op) (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_natop op (λne env, t) q env.
  Solve All Obligations with solve_proper.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | LitV n => interp_nat n
    | RecV e => interp_rec (interp_expr e)
    | ContV K => interp_cont_val (interp_cont K)
    end
  with
  interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | Val v => interp_val v
    | Var x => interp_var x
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
    | AppCont e1 e2 => interp_app_cont (interp_expr e1) (interp_expr e2)
    | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
    | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
    | Shift e => interp_shift (interp_expr e)
    | Reset e => interp_reset (interp_expr e)
    end
  with
  interp_cont {S} (K : cont S) : interp_scope S -n> (IT -n> IT) :=
    match K with
    | END => λne env x, x
    | IfK e1 e2 K => interp_ifk (interp_expr e1) (interp_expr e2) (interp_cont K)
    | AppLK e K => interp_applk (interp_expr e) (interp_cont K)
    | AppRK v K => interp_apprk (interp_val v) (interp_cont K)
    | AppContLK v K => interp_app_contlk (interp_val v) (interp_cont K)
    | AppContRK e K => interp_app_contrk (interp_expr e) (interp_cont K)
    | NatOpLK op v K => interp_natoplk op (interp_val v) (interp_cont K)
    | NatOpRK op e K => interp_natoprk op (interp_expr e) (interp_cont K)
    end.

  (** ** Interpretation of configurations *)

  Program Definition map_meta_cont {S} (mk : Mcont S) : @interp_scope F R _ S -n> state :=
    λne env, list_fmap _ _ (λ k, laterO_map (𝒫 ◎ (interp_cont k env))) mk.
  Next Obligation. intros S mk n ???. apply list_fmap_ext_ne. intro. by repeat f_equiv. Qed.

  Lemma map_meta_cont_nil {S} env :
    map_meta_cont ([] : Mcont S) env = [].
  Proof. done. Qed.

  Lemma map_meta_cont_cons {S} (k : cont S) (mk : Mcont S) env :
    map_meta_cont (k::mk) env = (laterO_map (𝒫 ◎ interp_cont k env)) :: (map_meta_cont mk env).
  Proof. done. Qed.

  Program Definition interp_config {S} (C : config S) : @interp_scope F R _  S -n> (prodO IT state) :=
      match C with
      | Cexpr e => λne env, (𝒫 (interp_expr e env), []) : prodO IT state
      | Ceval e K mk => λne env, (𝒫 (interp_cont K env (interp_expr e env)),
                                    map_meta_cont mk env)
      | Ccont K v mk => λne env, (𝒫 (interp_cont K env (interp_val v env)),
                                    map_meta_cont mk env)
      | Cmcont mk v => λne env, (𝒫 (interp_val v env),
                                   map_meta_cont mk env)
      | Cret v => λne env, (interp_val v env, [])
      end.
  Solve Obligations with try solve_proper.
  Next Obligation.
    intros S C e K mk <- n???. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros S C v K mk <- n???. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros S C v mk <- n???. by repeat f_equiv.
  Qed.


  Global Instance interp_val_asval {S} {D : interp_scope S} (v : val S)
    : AsVal (interp_val v D).
  Proof.
    destruct v; simpl.
    - apply _.
    - rewrite interp_rec_unfold. apply _.
    - apply _.
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
  with interp_cont_ren {S S'} env
         (δ : S [→] S') (K : cont S) :
    interp_cont (fmap δ K) env ≡ interp_cont K (ren_scope δ env).
  Proof.
    - destruct e; simpl; try by repeat f_equiv.
      + f_equiv; first by rewrite interp_expr_ren.
        intro; simpl.
        f_equiv; by rewrite interp_expr_ren.
      + f_equiv; last by rewrite interp_expr_ren.
        f_equiv. intro. simpl. by f_equiv.
      + f_equiv; last eauto. f_equiv. intro. simpl.
        rewrite !laterO_map_Next.
        repeat f_equiv.
        rewrite interp_expr_ren.
        f_equiv.
        intros [| ?]; simpl; first done.
        reflexivity.
    - destruct e; simpl.
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
        destruct y' as [| [| y]]; simpl; first done; last done.
        by iRewrite - "IH".
      + repeat f_equiv.
        intro. simpl. repeat f_equiv.
        apply interp_cont_ren.
    - destruct K; try solve [simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_ren || apply interp_val_ren || apply interp_cont_ren)].
      + intro. simpl. f_equiv; eauto.
        f_equiv; first by rewrite interp_val_ren.
        intro; simpl.
        reflexivity.
      + intro. simpl. f_equiv; eauto.
        f_equiv.
        intro; simpl.
        f_equiv.
        by rewrite interp_expr_ren.
      + simpl. intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv. intro. simpl. by repeat f_equiv.
      + simpl. intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv. intro. simpl. by repeat f_equiv.
  Qed.

  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : cont S):
    interp_expr (fill K e) env ≡ (interp_cont K) env ((interp_expr e) env).
  Proof. elim : K e env; eauto.
         - intros. simpl. rewrite H. f_equiv. simpl.
           f_equiv.
           intro; simpl.
           reflexivity.
         - intros. simpl. rewrite H. f_equiv. simpl.
           do 2 f_equiv. intro. simpl. by repeat f_equiv.
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
  with interp_cont_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') K :
    interp_cont (bind δ K) env ≡ interp_cont K (sub_scope δ env).
  Proof.
    - destruct e; simpl; try by repeat f_equiv.
      + f_equiv; first by rewrite interp_expr_subst.
        intro; simpl.
        f_equiv; first by rewrite interp_expr_subst.
      + f_equiv; last eauto. f_equiv. intro. simpl. by repeat f_equiv.
      + f_equiv; last eauto. f_equiv. intro. simpl.
        rewrite !laterO_map_Next.
        repeat f_equiv.
        rewrite interp_expr_subst.
        f_equiv.
        intros [| ?]; simpl; first done.
        rewrite interp_expr_ren.
        f_equiv.
        intros ?; simpl; done.
    - destruct e; simpl.
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
      + repeat f_equiv. intro. simpl. repeat f_equiv.
        by rewrite interp_cont_subst.
    - destruct K; try solve [simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_subst || apply interp_val_subst || apply interp_cont_subst)].
      + intro; simpl.
        f_equiv; first by rewrite interp_cont_subst.
        f_equiv; first by rewrite interp_val_subst.
        intro; simpl; reflexivity.
      + intro; simpl.
        f_equiv; first by rewrite interp_cont_subst.
        f_equiv.
        intro; simpl.
        f_equiv; first by rewrite interp_expr_subst.
      + simpl. intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv. intro. simpl. by repeat f_equiv.
      + simpl. intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv. intro. simpl. by repeat f_equiv.
  Qed.

  (** ** Interpretation of continuations is a homormophism *)

  #[local] Instance interp_cont_hom_emp {S} env :
    IT_hom (interp_cont (END : cont S) env).
  Proof.
    simple refine (IT_HOM _ _ _ _ _); intros; auto.
    simpl. f_equiv. intro. simpl.
    by rewrite laterO_map_id.
  Qed.

  #[local] Instance interp_cont_hom_if {S}
    (K : cont S) (e1 e2 : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (IfK e1 e2 K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite -hom_tick -IF_Tick.
    - trans (Vis op i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (IF t (interp_expr e1 env) (interp_expr e2 env)))
          y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      by rewrite -hom_vis.
    - trans (interp_cont K env (Err e)); first (f_equiv; apply IF_Err).
      apply hom_err.
  Qed.

  Transparent LET.
  #[local] Instance interp_cont_hom_appr {S} (K : cont S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppRK v K) env).
  Proof.
    pose proof (interp_val_asval v (D := env)) as HHH.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite <-hom_tick.
      f_equiv.
      rewrite /LET /LET_ne /=.
      rewrite ->2 get_val_ITV.
      simpl.
      rewrite get_val_tick.
      reflexivity.
    - rewrite /LET /LET_ne /=.
      rewrite get_val_ITV.
      simpl.
      rewrite ->2 hom_vis.
      f_equiv.
      intro; simpl.
      rewrite <-laterO_map_compose.
      do 2 f_equiv.
      intro; simpl.
      rewrite get_val_ITV.
      simpl.
      reflexivity.
    - rewrite <-hom_err.
      rewrite /LET /LET_ne /=.
      rewrite get_val_ITV.
      simpl.
      f_equiv.
      rewrite get_val_err.
      reflexivity.
  Qed.
  Opaque LET.

  Transparent LET.
  #[local] Instance interp_cont_hom_appl {S} (K : cont S)
    (e : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppLK e K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite <-hom_tick.
      f_equiv.
      rewrite /LET /LET_ne /=.
      rewrite get_val_tick.
      reflexivity.
    - rewrite /LET /LET_ne /=.
      rewrite !hom_vis.
      f_equiv.
      intro; simpl.
      rewrite <-laterO_map_compose.
      reflexivity.
    - rewrite <-hom_err.
      f_equiv.
      rewrite hom_err.
      rewrite /LET /LET_ne /=.
      rewrite get_val_err.
      reflexivity.
  Qed.
  Opaque LET.

  #[local] Instance interp_cont_hom_app_contr {S} (K : cont S)
    (e : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppContRK e K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite -!hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_cont_hom_app_contl {S} (K : cont S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppContLK v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv.
      rewrite get_val_ITV. simpl. rewrite hom_tick.
      f_equiv. by rewrite get_val_ITV.
    - rewrite get_val_ITV. simpl. rewrite get_fun_vis. rewrite hom_vis.
      f_equiv. intro. simpl. rewrite -laterO_map_compose.
      f_equiv. f_equiv. intro. simpl.
      f_equiv. by rewrite get_val_ITV.
    - rewrite get_val_ITV. simpl. rewrite get_fun_err. apply hom_err.
  Qed.

  #[local] Instance interp_cont_hom_natopr {S} (K : cont S)
    (e : expr S) op env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpRK op e K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_cont_hom_natopl {S} (K : cont S)
    (v : val S) op (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpLK op v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv. by rewrite -NATOP_ITV_Tick_l.
    - trans (Vis op0 i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (NATOP (do_natop op) t (interp_val v env))) y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      rewrite NATOP_ITV_Vis_l hom_vis. f_equiv. intro. simpl.
      by rewrite -laterO_map_compose.
    - trans (interp_cont K env (Err e)).
      + f_equiv. by apply NATOP_Err_l, interp_val_asval.
      + apply hom_err.
  Qed.

  #[global] Instance interp_cont_hom {S}
    (K : cont S) env :
    IT_hom (interp_cont K env).
  Proof.
    induction K; simpl; try apply _.
    by apply interp_cont_hom_appr.
  Qed.

  (** ** Finally, preservation of reductions *)
  Lemma interp_cred_no_reify {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) n :
    C ===> C' / (n, 0) ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    t ≡ Tick_n n $ t'.
  Proof.
    inversion 1; cbn-[IF LET APP' Tick get_ret2]; intros Ht Ht'; inversion Ht; inversion Ht'; try done.
    - do 3 f_equiv.
      intro; simpl.
      reflexivity.
    - do 4 f_equiv. intro. simpl. by repeat f_equiv.
    - rewrite -hom_tick. f_equiv.
      match goal with
      | |- context G [LET ?a ?b] =>
          set (F := b)
      end.
      trans (interp_cont k env (LET (Fun (Next (ir_unf (interp_expr e) env))) F)).
      {
        do 2 f_equiv.
        apply interp_rec_unfold.
      }
      subst F.
      rewrite LET_Val.
      simpl.
      rewrite LET_Val.
      simpl.
      rewrite APP'_Fun_l.
      rewrite laterO_map_Next.
      rewrite <-Tick_eq.
      rewrite hom_tick.
      do 2 f_equiv.
      simplify_eq.
      rewrite !interp_expr_subst.
      simpl.
      f_equiv.
      intros [| [| x]]; simpl; [| reflexivity | reflexivity].
      rewrite interp_val_ren.
      f_equiv.
      intros ?; simpl; reflexivity.
    - subst.
      destruct n0; simpl.
      + by rewrite IF_False; last lia.
      + by rewrite IF_True; last lia.
    - do 2 f_equiv. simplify_eq.
      destruct v1,v0; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
  Qed.

  Lemma interp_cred_no_reify_state {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) n :
    C ===> C' / (n, 0) ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    σ = σ'.
  Proof.
    inversion 1; cbn; intros Ht Ht'; inversion Ht; inversion Ht'; subst; reflexivity.
  Qed.

  Opaque map_meta_cont.
  Opaque extend_scope.

  Lemma interp_cred_yes_reify {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) (σr : gState_rest sR_idx rs ♯ IT) n :
    C ===> C' / (n, 1) ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    reify (gReifiers_sReifier rs) t (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ t', []).
  Proof.
    inversion 1; cbn-[IF APP' Tick get_ret2 gState_recomp]; intros Ht Ht'; inversion Ht; inversion Ht'; subst;
      try rewrite !map_meta_cont_cons in Ht, Ht'|-*.
    - trans (reify (gReifiers_sReifier rs)
               (RESET_ (laterO_map (𝒫 ◎ (interp_cont k env)))
               (Next (interp_expr e env)))
               (gState_recomp σr (sR_state (map_meta_cont mk env)))).
      {
        repeat f_equiv. rewrite !hom_vis. simpl. f_equiv.
        rewrite ccompose_id_l. by intro.
      }
      rewrite reify_vis_eq_ctx_dep//; last first.
      {
        epose proof (@subReifier_reify sz CtxDep reify_delim rs _ IT _ (op_reset)
                       (laterO_map 𝒫 (Next (interp_expr e env)))
                       _ (laterO_map (𝒫 ◎ interp_cont k env)) (map_meta_cont mk env)
                       (laterO_map (𝒫 ◎ interp_cont k env) :: map_meta_cont mk env) σr) as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last done.  solve_proper.
      }
      f_equiv; last done. by rewrite laterO_map_Next.
    - remember (map_meta_cont mk env) as σ.
      match goal with
      | |- context G [Vis ?o ?f ?κ] => set (fin := f); set (op := o); set (kout := κ)
      end.
      trans (reify (gReifiers_sReifier rs)
               (Vis op fin ((laterO_map (𝒫 ◎ interp_cont k env)) ◎ kout))
               (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv. rewrite !hom_vis. f_equiv. by intro.
      }
      rewrite reify_vis_eq_ctx_dep//; last first.
      {
        epose proof (@subReifier_reify sz CtxDep reify_delim rs _ IT _ (op_shift)
                       _ _ (laterO_map (𝒫 ◎ interp_cont k env))
                     σ σ σr) as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last first.
        - subst kout. by rewrite ccompose_id_l.
        - subst fin. reflexivity.
        - solve_proper.
      }
      simpl.
      rewrite -Tick_eq. do 3 f_equiv.
      rewrite interp_expr_subst.
      simpl. f_equiv. f_equiv.
      intros [|s]; simpl; eauto.
      Transparent extend_scope.
      simpl. f_equiv. f_equiv. by intro.
      Opaque extend_scope.
    - remember (map_meta_cont mk env) as σ.
      remember (laterO_map (𝒫 ◎ interp_cont k env)) as kk.
      match goal with
      | |- context G [ofe_mor_car _ _ (get_fun _)
                        (ofe_mor_car _ _ Fun ?f)] => set (fin := f)
      end.

      trans (reify (gReifiers_sReifier rs)
               (APP_CONT_ (Next (interp_val v env))
                  fin kk)
            (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv. rewrite get_val_ITV. simpl. rewrite get_fun_fun. simpl.
        rewrite !hom_vis. f_equiv. subst kk. rewrite ccompose_id_l. intro. simpl.
        rewrite laterO_map_compose. done.
      }
      rewrite reify_vis_eq_ctx_dep//; last first.
      {
        epose proof (@subReifier_reify sz CtxDep reify_delim rs _ IT _ (op_app_cont)
                       (Next (interp_val v env), fin) _ kk σ (kk :: σ) σr)
                    as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; eauto. solve_proper.
      }
      f_equiv; last done. by rewrite -!Tick_eq.
    - remember (map_meta_cont mk env) as σ.
      trans (reify (gReifiers_sReifier rs) (POP (interp_val v env))
               (gState_recomp σr (sR_state (laterO_map (𝒫 ◎ interp_cont k env) :: σ)))).
      {
        do 2 f_equiv; last repeat f_equiv.
        apply get_val_ITV.
      }
      rewrite reify_vis_eq_ctx_dep//; last first.
      {
        epose proof (@subReifier_reify sz CtxDep reify_delim rs _ IT _ (op_pop)
                       (Next (interp_val v env)) _ _
                       (laterO_map (𝒫 ◎ interp_cont k env) :: σ) σ σr)
                       as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last reflexivity.
        solve_proper.
      }
      f_equiv; last done. rewrite laterO_map_Next -Tick_eq.
      by f_equiv.
    - trans (reify (gReifiers_sReifier rs) (POP (interp_val v env))
               (gState_recomp σr (sR_state []))).
      {
        do 2 f_equiv; last first.
        { f_equiv. by rewrite map_meta_cont_nil. }
        apply get_val_ITV.
      }
      rewrite reify_vis_eq_ctx_dep//; last first.
      {
        epose proof (@subReifier_reify sz CtxDep reify_delim rs _ IT _ (op_pop)
                       (Next (interp_val v env)) _ _
                       [] [] σr)
                       as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last reflexivity.
        solve_proper.
      }
      f_equiv; last done. by rewrite -Tick_eq.
  Qed.


  (** * SOUNDNESS *)
  Lemma soundness {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) (σr : gState_rest sR_idx rs ♯ IT) n nm :
    steps C C' nm ->
    fst nm = n ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    external_steps (gReifiers_sReifier rs)
      t (gState_recomp σr (sR_state σ))
      t' (gState_recomp σr (sR_state σ')) [] n.
  Proof.
    intros H.
    revert n t t' σ σ'.
    induction (H); intros n0 t t' σ σ' Hnm Ht Ht'; subst; simpl.
    - rewrite Ht' in Ht. constructor; inversion Ht; done.
    - destruct (interp_config c2 env) as [t2 σ2] eqn:Heqc2.
      assert ((n', m').1 = n') as Hn' by done.
      rewrite <-Heqc2 in IHs.
      specialize (IHs s n' t2 t' σ2 σ' Hn' Heqc2 Ht').
      inversion H2; subst;
        try solve [specialize (interp_cred_no_reify env _ _ _ _ _ _ _ H2 Ht Heqc2) as Heq;
                   specialize (interp_cred_no_reify_state env _ _ _ _ _ _ _ H2 Ht Heqc2) as <-;
                   simpl in Heq|-*; rewrite Heq; eapply IHs];
        try solve
          [eapply reductions.steps_many with t2 (gState_recomp σr (sR_state σ2)) [] []; last done;
           first done;
            specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H2 Ht Heqc2) as Heq;
            cbn in Ht; eapply external_step_reify; last done;
           inversion Ht; rewrite !hom_vis; done].
      + eapply reductions.steps_many with t2 (gState_recomp σr (sR_state σ2)) [] [];
          last done; first done.
        specialize (interp_cred_no_reify env _ _ _ _ _ _ _ H2 Ht Heqc2) as Heq.
        specialize (interp_cred_no_reify_state env _ _ _ _ _ _ _ H2 Ht Heqc2) as <-.
        simpl in Heq|-*; rewrite Heq. constructor; eauto.
      + specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H2 Ht Heqc2) as Heq.
        simpl in Heq|-*.
        change (2+n') with (1+(1+n')).
        eapply reductions.steps_many; last first.
        * eapply reductions.steps_many with t2 (gState_recomp σr (sR_state σ2)) [] [];
            last done; first reflexivity.
          eapply external_step_tick; reflexivity.
        * eapply external_step_reify; last apply Heq.
          cbn in Ht. inversion Ht.
          rewrite get_val_ITV. simpl. rewrite get_fun_fun. simpl.
          rewrite !hom_vis. done.
        * done. 
      + eapply reductions.steps_many with t2 (gState_recomp σr (sR_state σ2)) [] [];
          last done; first done.
        specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H2 Ht Heqc2) as Heq.
        cbn in Ht; inversion Ht. subst. rewrite get_val_ITV. simpl.
        eapply external_step_reify; simpl in Heq; last first.
        * rewrite -Heq. f_equiv. f_equiv. rewrite get_val_ITV. simpl. done.
        * f_equiv. reflexivity.
      + eapply reductions.steps_many with t2 (gState_recomp σr (sR_state σ2)) [] [];
          last done; first done.
        specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H2 Ht Heqc2) as Heq.
        cbn in Ht; inversion Ht. subst. rewrite get_val_ITV. simpl.
        eapply external_step_reify; simpl in Heq; last first.
        * rewrite -Heq. repeat f_equiv. by rewrite get_val_ITV.
        * f_equiv. reflexivity.
  Qed.

End interp.
#[global] Opaque SHIFT_ RESET_ POP APP_CONT_.
