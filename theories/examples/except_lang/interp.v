From gitrees Require Import gitree lang_generic.
From iris.algebra Require Import list.
From gitrees.effects Require Export exceptions.
From gitrees.examples.except_lang Require Import lang.

Require Import Binding.Lib Binding.Set.


Module interp (Errors : ExcSig).

  Module _LANG := Lang Errors.
  Import _LANG.
  Import _Exc.
  
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
  Context {subE : subReifier reify_exc rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
      
  Global Instance denot_cont_ne (κ : IT -n> IT) :
    NonExpansive (λ x : IT, Tau (laterO_map κ (Next x))).
  Proof.
    solve_proper.
  Qed.

  (** Interpreting individual operators *)

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
    intros.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    do 3 f_equiv; intros ??; simpl; f_equiv;
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
    λne env, IF (t0 env) (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Ret n.

  Program Definition interp_throw {A} (err : exc) (e : A -n> IT) : A -n> IT :=
    λne env, THROW err (e env).
  Solve All Obligations with solve_proper.

  Global Instance interp_throw_ne A exc e : NonExpansive (@interp_throw A exc e).
  Proof. solve_proper. Qed.

  Program Definition interp_catch {A} (err : exc) (exp : (interp_scope A) -n> IT) (h : (@interp_scope F R _ (inc A)) -n> IT) : interp_scope A -n> IT :=
    λne env, CATCH err (λne (v : laterO IT), laterO_map (λne x, h (extend_scope env x) ) v) (exp env).
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intro a.
    simpl.
    destruct a; done.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; last done.
    intros a. simpl.
    repeat f_equiv.
    intros a2. simpl.
    repeat f_equiv.
    intros a3. simpl.
    destruct a3; done.
  Qed.

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

  Program Definition interp_throwk {A} (err : exc) (K : A -n> (IT -n> IT)) :
    A -n> (IT -n> IT) :=
    λne env t, interp_throw err (λne env, K env t) env.
  Next Obligation. Proof. solve_proper. Qed.
  Next Obligation.
  Proof.
    solve_proper_prepare.
    repeat f_equiv.
    solve_proper.
  Qed.
  Next Obligation. Proof. solve_proper. Qed.

  Program Definition interp_catchk {A} (err : exc) (K : interp_scope A -n> (IT -n> IT)) (h : interp_scope (inc A) -n> IT) :
    (interp_scope A) -n> (IT -n> IT) :=
    λne env t, interp_catch err (λne env, K env t) h env.
  Next Obligation. Proof. solve_proper. Qed.
  Next Obligation. Proof. solve_proper. Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; last done.
    intros a. simpl.
    repeat f_equiv.
    intros a2. simpl.
    repeat f_equiv.
    intros a3. simpl.
    destruct a3; done.
  Qed.
  
  (** Interpretation for all the syntactic categories: values, expressions, contexts **)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | LitV n => interp_nat n
    | RecV e => interp_rec (interp_expr e)
    end
  with interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
         match e with
         | Val v => interp_val v
         | Var x => interp_var x
         | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
         | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
         | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
         | Throw err v => interp_throw err (interp_expr v)
         | Catch err b h => interp_catch err (interp_expr b) (interp_expr h)
         end.

  Global Instance interp_val_asval {S} {v : val S} {env} : AsVal (interp_val v env).
  Proof.
    unfold AsVal.
    destruct v.
    - simpl. exists (RetV n). done.
    - simpl. unfold interp_rec.
      exists (FunV (Next (ir_unf (interp_expr e) env))).
      simpl.
      by rewrite interp_rec_unfold.
  Qed.

  Program Definition interp_handler {S} (h : expr (inc S)) : interp_scope S -n> laterO IT -n> laterO IT :=
    λne env, laterO_map (λne x, (interp_expr h) (extend_scope env x)).
  Next Obligation.
    solve_proper_prepare.
    f_equiv.
    intros []; simpl; solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intro.
    simpl.
    f_equiv.
    intros [];
      simpl; done.
    Qed.
  
  Program Fixpoint split_cont {S} (K : cont S) : interp_scope S → ((IT -n> IT) * (listO (excO * (laterO IT -n> laterO IT) * (laterO IT -n> laterO IT) )))%type :=
    λ env, 
    match K with
    | END => (idfun, [])
    | IfK e1 e2 K' => let (f, lst) := split_cont K' env in
                      (f ◎ (λne t, IF t
                                 (interp_expr e1 env)
                                 (interp_expr e2 env)), lst)
    | AppLK v K' => let (f, lst) := split_cont K' env in
                    (f ◎ (λne t, t ⊙ (interp_val v env)), lst)
    | AppRK e K' => let (f, lst) := split_cont K' env in
                    (f ◎ (λne t, (λne v, (interp_expr e env) ⊙ v) t), lst)
    | NatOpRK op e K' => let (f, lst) := split_cont K' env in
                         (f ◎ (λne t, NATOP (do_natop op) (interp_expr e env) t), lst)
    | NatOpLK op v K' => let (f, lst) := split_cont K' env in
                         (f ◎ (λne t, NATOP (do_natop op) t (interp_val v env)), lst)
                           
    | ThrowK err K' => let (f, lst) := split_cont K' env in
                       (f ◎ (λne t, THROW err t), lst)
    | CatchK err h K' => let (f, lst) := split_cont K' env in
                         (get_val (λne t, get_val (λne _, t) (_POP err)), (err,
                                      interp_handler h env  , laterO_map f)
                                  ::lst)
    end.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_please.
  Qed.

  Global Instance split_cont_ne  {S} {K : cont S} : NonExpansive (split_cont K).
  Proof.
    induction K; try done; intros n x y H; simpl;
      assert (Hs : split_cont K x ≡{n}≡ split_cont K y);
      try ( f_equiv; done );
      destruct (split_cont K x) as [f t];
      destruct (split_cont K y) as [f' t'];
      rewrite pair_dist in Hs;
      destruct Hs as [Hf Ht]; f_equiv; try done.
    - intro. simpl. repeat f_equiv; done.
    - intro. simpl. repeat f_equiv; done.
    - intro. simpl. repeat f_equiv; last done.
      intro. simpl. repeat f_equiv. done.
    - intro. simpl. repeat f_equiv; done.
    - intro. simpl. repeat f_equiv; done.
    - intro. simpl. repeat f_equiv; done.
    - repeat f_equiv; try done.
      intro x0. simpl. f_equiv. intro x1. simpl. destruct x1; first done.
      f_equiv. done.
  Qed.

  Theorem split_cont_left_hom {S} {K : cont S} {env : interp_scope S}
    : IT_hom (split_cont K env).1 .
  Proof.
    induction K.
    - simple refine (IT_HOM _ _ _ _ _);
        intros;
        simpl;
        repeat f_equiv.
      change (λne x : IT, x) with (@idfun IT).
      intros x.
      rewrite /ccompose /compose /=.
      apply laterO_map_id.
    - simpl.
      specialize (IHK env).
      destruct (split_cont K env) as [f t] eqn:Heq.
      simpl in *.
      simple refine (IT_HOM _ _ _ _ _).
      + intros. simpl.
        rewrite IF_Tick.
        apply IHK.
      + intros. simpl.
        rewrite IF_Vis hom_vis.
        f_equiv.
        rewrite !/ccompose !/compose /=.
        intros x. simpl.
        rewrite -laterO_map_compose.
        repeat f_equiv.
        intro.
        simpl.
        done.
      + intros e. simpl.
        rewrite IF_Err.
        apply IHK.
    - simpl.
      specialize (IHK env).
      destruct (split_cont K env) as [f t] eqn:Heq.
      simpl in *.
      simple refine (IT_HOM _ _ _ _ _); intros; simpl.
      + rewrite APP'_Tick_l.
        apply IHK.
      + rewrite APP'_Vis_l hom_vis.
        f_equiv.
        rewrite !/ccompose !/compose /=.
        intro. simpl.
        rewrite -laterO_map_compose.
        f_equiv.
        intro. done.
      + rewrite APP'_Err_l. apply IHK.
    - simpl.
      specialize (IHK env).
      destruct (split_cont K env) as [f t] eqn:Heq.
      simpl in *.
      rewrite /compose.
      refine (IT_HOM _ _ _ _ _); intros; simpl.
      + rewrite APP'_Tick_r. apply hom_tick.
      + rewrite APP'_Vis_r hom_vis.
        f_equiv.
        intro. simpl.
        rewrite laterO_map_compose.
        f_equiv.
        intro. done.
      + rewrite APP'_Err_r. apply hom_err.
    - simpl.
      specialize (IHK env).
      destruct (split_cont K env) as [f t] eqn:Heq.
      simpl in *.
      rewrite /compose.
      refine (IT_HOM _ _ _ _ _); intros; simpl.
      + rewrite NATOP_ITV_Tick_l.
        apply hom_tick.
      + rewrite NATOP_ITV_Vis_l hom_vis.
        f_equiv.
        intro. simpl.
        rewrite -laterO_map_compose.
        do 2 f_equiv. intro. simpl. done.
      + rewrite NATOP_Err_l.
        apply hom_err.
    - simpl.
      specialize (IHK env).
      destruct (split_cont K env) as [f t] eqn:Heq.
      simpl in *.
      rewrite /compose.
      refine (IT_HOM _ _ _ _ _); intros; simpl.
      +  by rewrite -hom_tick NATOP_Tick_r.
      + rewrite NATOP_Vis_r hom_vis.
        f_equiv.
        intro. simpl.
        rewrite laterO_map_compose.
        f_equiv. intro. done.
      + rewrite NATOP_Err_r.
        apply hom_err.
     - simpl.
      specialize (IHK env).
      destruct (split_cont K env) as [f t] eqn:Heq.
      simpl in *.
      rewrite /compose.
      refine (IT_HOM _ _ _ _ _); intros; simpl.
       + do 2 rewrite hom_tick.
         done.
       + do 2 rewrite hom_vis.
         f_equiv.
         intro. simpl.
         rewrite -laterO_map_compose.
         f_equiv.
         intros [].
         done.
       + by do 2 rewrite hom_err.
     - simpl.
       destruct (split_cont K env) as [f t] eqn:Heq.
       simpl in *.
      refine (IT_HOM _ _ _ _ _); intros; simpl.
       + by rewrite -hom_tick.
       + rewrite hom_vis.
         do 3 f_equiv. intro. simpl. done.
       + by rewrite hom_err.
  Qed.

  Theorem split_cont_left_hom' {S} {K : cont S} {env} f t : split_cont K env = (f,t) → IT_hom f.
  Proof.
    intros H.
    replace f with (split_cont K env).1.
    - apply split_cont_left_hom.
    - rewrite H. done.
  Qed.
         
  Program Definition interp_config {S} (cfg : @config S) : interp_scope S -n> (IT * stateF ♯ IT)%type :=
    match cfg with
    | Cexpr e => λne env, (interp_expr e env, [])
    | Ceval e K => λne env, let (f,t) := split_cont K env in
                            (f (interp_expr e env), t)
    | Ccont K v => λne env, let (f,t) := split_cont K env in
                            (f (interp_val v env), t)
    | Cret v => λne env, (interp_val v env, [])
    end.
  Solve All Obligations with try solve_proper.
  Next Obligation.
  Proof.
    solve_proper_prepare.
    assert (Hs : split_cont K x ≡{n}≡ split_cont K y). { f_equiv. done. }
    destruct (split_cont K x) as [f t].
    destruct (split_cont K y) as [f' t'].
    rewrite pair_dist in Hs.
    destruct Hs as [Hf Ht].
    repeat f_equiv; done.
  Qed.
  Next Obligation.
  Proof.
    solve_proper_prepare.
    assert (Hs : split_cont K x ≡{n}≡ split_cont K y). { f_equiv. done. }
    destruct (split_cont K x) as [f t].
    destruct (split_cont K y) as [f' t'].
    rewrite pair_dist in Hs.
    destruct Hs as [Hf Ht].
    repeat f_equiv; done.
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
    interp_val (fmap δ e) env ≡ interp_val e (ren_scope δ env).
  (** with interp_cont_ren {S S'} env
         (δ : S [→] S') (e : cont S) :
    interp_cont (fmap δ e) env ≡ interp_cont e (ren_scope δ env). **)
  Proof.
    - destruct e; simpl.
      + by apply interp_val_ren.
      + reflexivity.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv.
        * intros [].  simpl. do 2 rewrite laterO_map_Next.
          f_equiv. simpl.
          rewrite interp_expr_ren.
          f_equiv.
          intros []; by simpl.
        * apply interp_expr_ren.
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
        destruct y' as [| [| y]]; simpl; first done.
        * by iRewrite - "IH".
        * done.
    (* - destruct e; simpl; intros ?; simpl.
      + reflexivity.
      + repeat f_equiv; [by apply interp_cont_ren | by apply interp_expr_ren | by apply interp_expr_ren].
      + repeat f_equiv; [by apply interp_cont_ren | by apply interp_val_ren].
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_cont_ren].
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_cont_ren].
      + repeat f_equiv; [by apply interp_cont_ren | by apply interp_val_ren].
      + repeat f_equiv. by apply interp_cont_ren.
      + repeat f_equiv; last done.
        intro.
        simpl.
        destruct x0.
        do 2 rewrite laterO_map_Next.
        f_equiv.
        simpl.
        rewrite interp_expr_ren.
        f_equiv.
        intro.
        destruct x0; done. *)
  Qed.
(*
  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : cont S):
    interp_expr (fill K e) env ≡ (interp_cont K) env ((interp_expr e) env).
  Proof.
    revert env.
    induction K; simpl; intros env; first reflexivity; try (by rewrite IHK).
    - repeat f_equiv.
      by rewrite IHK.
    - repeat f_equiv.
      by rewrite IHK.
    - repeat f_equiv.
      by rewrite IHK.
  Qed.
*)
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
    interp_val (bind δ e) env ≡ interp_val e (sub_scope δ env).
(*  with interp_cont_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') e :
    interp_cont (bind δ e) env ≡ interp_cont e (sub_scope δ env). *)
  Proof.
    - destruct e; simpl.
      + by apply interp_val_subst.
      + term_simpl.
        reflexivity.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; by apply interp_expr_subst.
      + repeat f_equiv; last done.
        intros [].
        do 2 rewrite laterO_map_Next.
        f_equiv.
        simpl.
        rewrite interp_expr_subst.
        f_equiv.
        intros []; simpl.
        * done.
        * rewrite interp_expr_ren.
          f_equiv.
          intro.
          simpl.
          done.
          
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
   (* - destruct e; simpl; intros ?; simpl.
      + reflexivity.
      + repeat f_equiv; [by apply interp_cont_subst | by apply interp_expr_subst | by apply interp_expr_subst].
      + repeat f_equiv; [by apply interp_cont_subst | by apply interp_val_subst].
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_cont_subst].
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_cont_subst].
      + repeat f_equiv; [by apply interp_cont_subst | by apply interp_val_subst].
      + repeat f_equiv.
        by apply interp_cont_subst.
      + repeat f_equiv; last done.
        intros []. simpl.
        do 2 rewrite laterO_map_Next.
        f_equiv. simpl.
        rewrite interp_expr_subst.
        f_equiv.
        intros []; simpl.
        * done.
        * rewrite interp_expr_ren.
          f_equiv.
          by intro. *)
  Qed.

  Lemma split_cont_decomp {S} K K1 K2 p t p1 t1 env h err f k:
    split_cont K env = (p,t) →
    split_cont K1 env = (p1,t1) →
    K = cont_compose (CatchK err h K1) K2 →
    (∀ K4 K3 h', K2 <> @cont_compose S (CatchK err h' K3) K4) →
    f = interp_handler h env →
    k = laterO_map p1 → 
    ∃pre, t = pre ++ (err,f,k)::t1 ∧ Forall (λ '(err', _ ,_ ), err <> err' ) pre.
  Proof.
    generalize dependent K1.
    generalize dependent p.
    generalize dependent t.
    generalize dependent p1.
    generalize dependent t1.
    generalize dependent K2.
    generalize dependent f.
    generalize dependent env.
    generalize dependent h.
      
    induction K; intros.
    - destruct K2; discriminate.
    - destruct K2; try discriminate.
      injection H1 as <- <- ->.
      simpl in H.
      destruct (split_cont (cont_compose (CatchK err h K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      eapply (IHK h env _ _ _ _ u g _ Heq H0 eq_refl).
      Unshelve.
      2, 3 : done.
      intros K4 K3 h' C.
      rewrite C in H2.
      eapply (H2 (IfK e₁ e₂ K4)).
      simpl.
      reflexivity.
    - destruct K2; try discriminate.
      injection H1 as <- ->.
      simpl in H.
      destruct (split_cont (cont_compose (CatchK err h K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      eapply (IHK h env _ _ _ _ u g _ Heq H0 eq_refl).
      Unshelve.
      2, 3 : done.
      intros K4 K3 h' C.
      rewrite C in H2.
      eapply (H2 (AppLK v K4)).
      simpl.
      reflexivity.
    - destruct K2; try discriminate.
      injection H1 as <- ->.
      simpl in H.
      destruct (split_cont (cont_compose (CatchK err h K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      eapply (IHK h env _ _ _ _ u g _ Heq H0 eq_refl).
      Unshelve.
      2, 3 : done.
      intros K4 K3 h' C.
      rewrite C in H2.
      eapply (H2 (AppRK e K4)).
      simpl.
      reflexivity.
    - destruct K2; try discriminate.
      injection H1 as <- <- ->.
      simpl in H.
      destruct (split_cont (cont_compose (CatchK err h K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      eapply (IHK h env _ _ _ _ u g _ Heq H0 eq_refl).
      Unshelve.
      2, 3 : done.
      intros K4 K3 h' C.
      rewrite C in H2.
      eapply (H2 (NatOpLK op v K4)).
      simpl.
      reflexivity.
    - destruct K2; try discriminate.
      injection H1 as <- <- ->.
      simpl in H.
      destruct (split_cont (cont_compose (CatchK err h K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      eapply (IHK h env _ _ _ _ u g _ Heq H0 eq_refl).
      Unshelve.
      2, 3 : done.
      intros K4 K3 h' C.
      rewrite C in H2.
      eapply (H2 (NatOpRK op e K4)).
      simpl.
      reflexivity.      
    - destruct K2; try discriminate.
      injection H1 as <- ->.
      simpl in H.
      destruct (split_cont (cont_compose (CatchK err h K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      eapply (IHK h env _ _ _ _ u g _ Heq H0 eq_refl).
      Unshelve.
      2, 3 : done.
      intros K4 K3 h' C.
      rewrite C in H2.
      eapply (H2 (ThrowK err0 K4)).
      simpl.
      reflexivity.

     - destruct K2; try discriminate.
     + injection H1 as <- <- ->.
       simpl in H.
       rewrite H0 in H.
       injection H as <- <-.
       eexists [].
       rewrite H3 H4.
       simpl.
       done.
     + injection H1 as <- <- ->.
       simpl in H.
       destruct (split_cont (cont_compose (CatchK err h0 K1) K2) env) as [g u] eqn:Heq.
      injection H as <- <-.
      epose proof (IHK h0 env _ _ _ _ u g _ Heq H0 _ _ _ _) as (pre & -> & Hfall).
      eexists.
      split.
      { rewrite app_comm_cons. done. }
      apply Forall_cons.
      split; last done.
      intros ->.
      by eapply (H2 END).
      Unshelve.
      2, 4, 5 : done.
       intros K4 K3 h' C.
       rewrite C in H2.
       eapply (H2 (CatchK err0 h K4) _).
       simpl.
       done.
  Qed.

  Lemma unwind_cut_when {S} : ∀ K K' env f t g t' err h,
    split_cont K env = (f,t) →
    split_cont K' env = (g,t') →
    @unwind S err K = Some (h, K') →
    cut_when (aux err) t = Some ((err,interp_handler h env,laterO_map g), t').
  Proof.
    intros K K' env f t g t' err h HsplitK HsplitK' Hwind.
    apply unwind_decompose in Hwind as (K1 & -> & HK1).
    pose proof (split_cont_decomp _ _ _ f t g t' env h err _ _ HsplitK HsplitK' eq_refl HK1 eq_refl eq_refl) as (pre & -> & Hfall).
    eapply cut_when_first_occ.
    { done. }
    { simpl. destruct (eq_dec err err); done. }.
    eapply Forall_impl.
    { exact Hfall. }
    intros [[err' ?] ?] ?.
    simpl.
    destruct (eq_dec err err'); done.
  Qed.
    
  Theorem soundness {S} : ∀ c c' e e' σr σ σ' (env : interp_scope S),
    interp_config c env = (e, σ) → 
    interp_config c' env = (e', σ') → 
    c ===> c' →
    ∃ n, 
      ssteps (gReifiers_sReifier rs)
              e (gState_recomp σr (sR_state σ))
              e' (gState_recomp σr (sR_state σ')) n.
  Proof.
    intros.
    revert H H0.
    induction H1; intros H0 H1. 
    - simpl in H0, H1.
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; done.
    - simpl in H0, H1.
      rewrite H0 in H1.
      injection H1 as <- <-.
      exists 0.
      constructor; done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [f t].
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [f t].
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [f t].
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [f t] eqn:Heq.
      assert (IT_hom f).
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 1.
      econstructor.
      + rewrite hom_vis.
        eapply sstep_reify; first done.
        rewrite reify_vis_eq_ctx_dep.
        { rewrite Tick_eq. done. }
        epose (@subReifier_reify _ _ _ _ _ _ _ (inl ()) ?[x] (Next _) ?[k] t ?[σ'] σr _) as Hry.
        match goal with
        | |- _ _ _ (_ ?x', (_ _ (_ ?σ2)) , ?k' ◎ _) ≡ _ =>  instantiate (x := x');
                                                            instantiate (k := k')
                                                        
        end.
        Unshelve.
        6 : { simpl. done. }.
        1 : { simpl in Hry|-*.
              erewrite <-Hry.
              repeat f_equiv; first by solve_proper.
              intro. simpl. done.
        }
      + constructor.
        * repeat f_equiv.
          intro. simpl.
          f_equiv.
          f_equiv. (* Reflexivity doesn't work here, really funny, show Sergei *)
          intro.
          simpl.
          done.
        * simpl.
          do 5 f_equiv;
          f_equiv;
          intro;
          simpl;
          done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [f t] eqn:Heq.
      assert (IT_hom f).
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      by constructor.
    - simpl in H0, H1.
      destruct (split_cont k env) as [f t] eqn:Heq.
      assert (IT_hom f).
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      by constructor.
    - simpl in H0, H1.
      destruct (split_cont k env) as [g t] eqn:Heq.
      assert (IT_hom g) as Hg.
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 1.
      econstructor; last (econstructor; reflexivity).
      apply sstep_tick; last done.
      rewrite -hom_tick.
      f_equiv.
      pose (interp_rec_unfold (interp_expr f) env) as H.
      assert (∀ x y z : IT, x ≡ y → x ⊙ z ≡ y ⊙ z) as APP'_equiv.
      { intros x y z Hxy.
        Transparent APP APP'.
        simpl.
        Opaque APP APP'.
        repeat f_equiv.
        intro. simpl.
        f_equiv.
        done.
     } 
     rewrite (APP'_equiv _ _ _ H) APP_APP'_ITV APP_Fun Tick_eq /=.
     do 2 rewrite interp_expr_subst.
     do 3 f_equiv.
     intros [].
     + simpl. rewrite -interp_val_subst.
       do 2 f_equiv.
       pose @subst_shift_id as Hsbs.
       unfold subst in Hsbs.
       rewrite Hsbs.
       done.
     + destruct i; simpl.
       * done.
       * done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [g t] eqn:Heq.
      assert (IT_hom g) as Hg.
      { eapply split_cont_left_hom'. apply Heq. }
     injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; last done.
      f_equiv.
      destruct n.
      + rewrite IF_False; last lia.
        done.
      + rewrite IF_True; last lia.
        done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [g t] eqn:Heq.
      assert (IT_hom g) as Hg.
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; done.
    - simpl in H0, H1.
      destruct (split_cont k env) as [g t] eqn:Heq.
      assert (IT_hom g) as Hg.
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 0.
      constructor; last done.
      f_equiv.
      destruct v1, v2.
      2, 3, 4 : contradict H; done.
      simpl in H.
      injection H as <-.
      simpl.
      apply NATOP_Ret.
    - simpl in H0, H1.
      destruct (split_cont k env) as [g t] eqn:Heq.
      assert (IT_hom g) as Hg.
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 1.
      econstructor; last (constructor; done).
      rewrite get_val_ITV /= get_val_vis.
      eapply sstep_reify; first done.
      rewrite reify_vis_eq_ctx_dep.
      { rewrite Tick_eq. done. }
      epose proof (@subReifier_reify _ _ _ _ _ _ _ (inr (inl ())) ?[x] (Next _) ?[k] ?[σ] ?[σ'] σr _) as Hry.
      match goal with
      | |- _ _ _ (_ ?x', (_ _ (_ (_ ?σ2) _)) , ?k1 ◎ (?k2 ◎ _)) ≡ _ =>  instantiate (x := x');
                                                                        instantiate (k := k1 ◎ k2);
                                                                        instantiate (σ := σ2)
                                                                                    
      end.
      Unshelve.
      4 : { simpl. destruct (eq_dec err) as [? | ?]; done. }.
      1 : { simpl in Hry|-*.
            match goal with
            | [Hry : _ ≡ ?r |- _ ] => transitivity r
            end.
            2 : { repeat f_equiv.
                  Transparent laterO_map.
                  simpl.
                  Opaque laterO_map.
                  f_equiv.
                  apply get_val_ret.
            }
            
            rewrite -Hry.
            
            repeat f_equiv; first by solve_proper.
            intro. simpl. done.
      }
    - simpl in H0, H1.
      (** (interp_expr (subst h (Val v)) env), t) **)
      destruct (split_cont k env) as [g t] eqn:Heq.
      destruct (split_cont k' env) as [g' t'] eqn:Heq'.
      assert (IT_hom g) as Hg.
      { eapply split_cont_left_hom'. apply Heq. }
      injection H0 as <- <-.
      injection H1 as <- <-.
      exists 1.
      econstructor; last by constructor.
      rewrite get_val_ITV hom_vis.
      eapply sstep_reify; first done.
      rewrite reify_vis_eq_ctx_dep.
      { rewrite Tick_eq. done. }
      epose proof (@subReifier_reify _ _ _ _ _ _ _ (inr (inr (inl ()))) ?[x] (Next _) ?[k] ?[σ] t' σr _) as Hry.
      match goal with
      | |- _ _ _ (_ ?x', (_ _ (_ _ ?σ2)) , _) ≡ _ =>
          instantiate (x := x');
          instantiate (σ := σ2)
      end.
      Unshelve.
      4 : { Opaque cut_when. simpl. 
            apply (unwind_cut_when _ _ env _ _ _ _ _ _ Heq Heq') in H.
            rewrite H.
            simpl.
            f_equiv.
            rewrite laterO_map_Next.
            simpl.
            rewrite pair_equiv.
            split; last done.
            f_equiv.
            trans (g' (interp_expr (subst h (Val v)) env)); last done.
            f_equiv.
            rewrite interp_expr_subst.
            f_equiv.
            intros []; done.
      }
      1 : {
        simpl in Hry.
        simpl.
        rewrite -Hry.
        repeat f_equiv; first solve_proper.
        intro.
        simpl.
        instantiate (k := (laterO_map (λne y, g y)) ◎  (λne x, Empty_set_rect (λ _ : ∅, laterO IT) x)).
        simpl.
        done.
        Unshelve.
        intros n [].
      }
      
  Qed.


     
  

     

 
      

      

      
     
      

          
        
        
        
        

  
  (** ** Interpretation of evaluation contexts induces homomorphism *)

  #[local] Instance interp_cont_hom_emp {S} env :
    IT_hom (interp_cont (EmptyIK : cont S) env).
  Proof.
    simple refine (IT_HOM _ _ _ _ _); intros; auto.
    simpl. fold (@idfun IT). f_equiv. intro. simpl.
    by rewrite laterO_map_id.
  Qed.

  #[local] Instance interp_cont_hom_if {S}
    (K : cont S) (e1 e2 : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (IfIK K e1 e2) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -IF_Tick. do 3 f_equiv. apply hom_tick.
    - assert ((interp_cont K env (Vis op i ko)) ≡
        (Vis op i (laterO_map (λne y, interp_cont K env y) ◎ ko))).
      { by rewrite hom_vis. }
      trans (IF (Vis op i (laterO_map (λne y : IT, interp_cont K env y) ◎ ko))
               (interp_expr e1 env) (interp_expr e2 env)).
      { do 3 f_equiv. by rewrite hom_vis. }
      rewrite IF_Vis. f_equiv. simpl.
      intro. simpl. by rewrite -laterO_map_compose.
    - trans (IF (Err e) (interp_expr e1 env) (interp_expr e2 env)).
      { repeat f_equiv. apply hom_err. }
      apply IF_Err.
  Qed.

  #[local] Instance interp_cont_hom_appr {S} (K : cont S)
    (e : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppRIK e K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_cont_hom_appl {S} (K : cont S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppLIK K v) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -APP'_Tick_l. do 2 f_equiv. apply hom_tick.
    - trans (APP' (Vis op i (laterO_map (interp_cont K env) ◎ ko))
               (interp_val v env)).
      + do 2f_equiv. rewrite hom_vis. do 3 f_equiv. by intro.
      + rewrite APP'_Vis_l. f_equiv. intro x. simpl.
        by rewrite -laterO_map_compose.
    - trans (APP' (Err e) (interp_val v env)).
      { do 2f_equiv. apply hom_err. }
      apply APP'_Err_l, interp_val_asval.
  Qed.

  #[local] Instance interp_cont_hom_natopr {S} (K : cont S)
    (e : expr S) op env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpRIK op e K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_cont_hom_natopl {S} (K : cont S)
    (v : val S) op (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpLIK op K v) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -NATOP_ITV_Tick_l. do 2 f_equiv. apply hom_tick.
    - trans (NATOP (do_natop op)
               (Vis op0 i (laterO_map (interp_cont K env) ◎ ko))
               (interp_val v env)).
      { do 2 f_equiv. rewrite hom_vis. f_equiv. by intro. }
      rewrite NATOP_ITV_Vis_l. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - trans (NATOP (do_natop op) (Err e) (interp_val v env)).
      + do 2 f_equiv. apply hom_err.
      + by apply NATOP_Err_l, interp_val_asval.
  Qed.

  #[local] Instance interp_cont_hom_throw {S} (K : cont S) err (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (ThrowIK err K) env).
  Proof.
    Opaque THROW.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by do 2 rewrite hom_tick.
    - do 2 rewrite hom_vis. f_equiv. by intro.
    - by do 2 rewrite hom_err.
  Qed.

  
  #[global] Instance interp_cont_hom {S} (IK : cont S) env :
    (∃ K, IK = cont_of_cont K) →
    IT_hom (interp_cont IK env).
  Proof.
    intros [K ->].
    induction K; try apply _.
  Qed.

  (** ** Finally, preservation of reductions *)
  Lemma interp_expr_head_step {S : Set} (env : interp_scope S) (e : expr S) e' n :
    head_step e e' (n, 0) →
    interp_expr e env ≡ Tick_n n $ interp_expr e' env.
  Proof.
    inversion 1; cbn-[IF APP' INPUT Tick get_ret2].
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
    - (* the natop stuff *)
      simplify_eq.
      destruct v1,v2; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
    - rewrite IF_True; last lia.
      reflexivity.
    - rewrite IF_False; last lia.
      reflexivity.
  Qed.

  Lemma interp_expr_fill_no_reify {S} K (env : interp_scope S) (e e' : expr S) n :
    head_step e e' (n, 0) →
    interp_expr (fill (cont_of_cont K) e) env
      ≡
      Tick_n n $ interp_expr (fill (cont_of_cont K) e') env.
  Proof.
    intros He.
    rewrite !interp_comp.
    erewrite <-hom_tick_n.
    - apply (interp_expr_head_step env) in He.
      rewrite He.
      reflexivity.
    - apply interp_cont_hom. exists K. done.
  Qed.

  Opaque extend_scope.
  Opaque Ret.
 (**
  Lemma interp_expr_fill_yes_reify {S} K env (e e' : expr S)
    (σ σ' : stateO) (σr : gState_rest sR_idx rs ♯ IT) n :
    head_step e e' (n, 1) →
    reify (gReifiers_sReifier rs)
      (interp_expr (fill K e) env) (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K e') env).
  Proof.
    intros Hst.
    trans (reify (gReifiers_sReifier rs) (interp_cont K env (interp_expr e env))
             (gState_recomp σr (sR_state σ))).
    { f_equiv. by rewrite interp_comp. }
    inversion Hst; simplify_eq; cbn-[gState_recomp].
    - trans (reify (gReifiers_sReifier rs) (INPUT (interp_cont K env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv; eauto.
        rewrite hom_INPUT.
        do 2 f_equiv. by intro.
      }
      rewrite reify_vis_eq_ctx_indep //; first last.
      {
        epose proof (@subReifier_reify sz NotCtxDep reify_io rs _ IT _ (inl ()) () _ σ σ' σr) as H.
        simpl in H.
        simpl.
        erewrite <-H; last first.
        - rewrite H4. reflexivity.
        - f_equiv;
          solve_proper.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      rewrite ofe_iso_21.
      simpl.
      reflexivity.
    - trans (reify (gReifiers_sReifier rs) (interp_cont K env (OUTPUT n0)) (gState_recomp σr (sR_state σ))).
      {
        do 3 f_equiv; eauto.
        rewrite get_ret_ret//.
      }
      trans (reify (gReifiers_sReifier rs) (OUTPUT_ n0 (interp_cont K env (Ret 0))) (gState_recomp σr (sR_state σ))).
      {
        do 2 f_equiv; eauto.
        by rewrite hom_OUTPUT_.
      }
      rewrite reify_vis_eq_ctx_indep //; last first.
      {
        epose proof (@subReifier_reify sz _ reify_io rs _ IT _ (inr (inl ())) n0 _ σ (update_output n0 σ) σr) as H.
        simpl in H.
        simpl.
        erewrite <-H; last reflexivity.
        f_equiv.
        intros ???. by rewrite /prod_map H0.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
  Qed.
  *)

  Example test1 err : expr ∅ :=
    (try
       (#4) + #5
      catch err => #1
    )%syn.
  
  Example test2 err : expr ∅ :=
    (try
       #9
      catch err => #1
    )%syn.

  Example uu err σr : ∃ n m σ t,
      ssteps (gReifiers_sReifier rs)
        (interp_expr (test1 err) (λne (x : leibnizO ∅), match x with end) : IT)
        (gState_recomp σr (sR_state σ))
        t 
        (gState_recomp σr (sR_state σ)) n ∧
      ssteps (gReifiers_sReifier rs)
        (interp_expr (test2 err) (λne (x : leibnizO ∅), match x with end) : IT)
        (gState_recomp σr (sR_state σ))
        t 
        (gState_recomp σr (sR_state σ)) m.
  Proof.
    rewrite /test1 /test2.
    simpl.
    do 2 eexists.
    exists [].
    eexists.
    split.
    - eapply ssteps_many.
      + eapply sstep_reify.
        { f_equiv. rewrite /ccompose /compose /=. reflexivity. }.
        Check reify_vis_eq_ctx_dep.
        apply reify_vis_eq_ctx_dep.
        


  Proof.
    intros H.
    unfold test1 in H.
    unfold test2 in H.
    simpl in H.
  
  Compute .
  
  Lemma soundness {S} (e1 e2 : expr S) (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) :
    prim_step e1 e2 (n,m) → ∀ σ1, ∃ σ2,
    ssteps (gReifiers_sReifier rs)
              (interp_expr e1 env) (gState_recomp σr (sR_state σ1))
              (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n.
  Proof.
    Opaque gState_decomp gState_recomp.
    intros Hstep.
    inversion Hstep;simplify_eq/=.
    - intros σ1.
      eexists.
      rewrite !interp_comp.
      

    
     unshelve eapply (interp_expr_fill_no_reify K) in H2; first apply env.
       rewrite H2.
       rewrite interp_comp.
       eapply ssteps_tick_n.
     + inversion H2;subst.
       * eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
         rewrite interp_comp.
         rewrite hom_INPUT.
         change 1 with (Nat.add 1 0). econstructor; last first.
         { apply ssteps_zero; reflexivity. }
         eapply sstep_reify.
         { Transparent INPUT. unfold INPUT. simpl.
           f_equiv. reflexivity. }
         simpl in H2.
         rewrite -H2.
         repeat f_equiv; eauto.
         rewrite interp_comp hom_INPUT.
         eauto.
       * eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
         rewrite interp_comp. simpl.
         rewrite get_ret_ret.
         rewrite hom_OUTPUT_.
         change 1 with (Nat.add 1 0). econstructor; last first.
         { apply ssteps_zero; reflexivity. }
         eapply sstep_reify.
         { Transparent OUTPUT_. unfold OUTPUT_. simpl.
           f_equiv. reflexivity. }
         simpl in H2.
         rewrite -H2.
         repeat f_equiv; eauto.
         Opaque OUTPUT_.
         rewrite interp_comp /= get_ret_ret hom_OUTPUT_.
         eauto.
  Qed.
   

  Section Examples.
    Context `{!invGS Σ, !stateG rs R Σ}.

    Opaque CATCH.
    
    Example prog1 (err : exc) (n : nat) : expr ∅ :=
      (try
         if #n then
          throw err #5
         else #4
       catch err => ($0) * $0
      )%syn.
    
    Example wp_prog1 (err : exc) (n : nat) (σ : stateF ♯ IT) Φ :
      has_substate σ -∗
      ▷(£1 -∗ has_substate σ -∗ (⌜n = 0⌝ -∗ Φ (RetV 4)) ∗ (⌜n > 0⌝ -∗  Φ (RetV 25))) -∗
      WP@{rs} (interp_expr (prog1 err n) (λne (x : leibnizO ∅), match x with end) : IT) {{ Φ }}.
    iIntros "Hσ H▷".
    simpl.
    destruct n.
    - rewrite IF_False; last lia.
      iApply (wp_catch_v _ _ (Ret 4) _ _ _ idfun with "Hσ").
      + by simpl.
      + iIntros "!> H£ Hσ".
        iPoseProof ("H▷" with "H£ Hσ") as "[HΦ _]".
        iApply wp_val.
        iModIntro.
        by iApply "HΦ".
    - rewrite IF_True; last lia.
      iApply (wp_catch_throw _ _ (Ret 5) idfun idfun with "Hσ").
      + simpl.
        rewrite laterO_map_Next.
        simpl.
        rewrite NATOP_Ret.
        by simpl.
      + simpl.
        iIntros "!> H£ Hσ".
        iPoseProof ("H▷" with "H£ Hσ") as "[_ HΦ]".
        iApply wp_val.
        iModIntro.
        iApply "HΦ".
        iPureIntro.
        lia.
    Qed.

    Example prog2 (err : exc) : expr ∅ :=
      (if (
           try 
             throw err #3
           catch err => ($0) * #4  
         )
       then #1
       else #0
      )%syn.
    
    Example wp_prog2 (err : exc) (σ : stateF ♯ IT) Φ :
      has_substate σ -∗
      ▷(£1 -∗ has_substate σ -∗ Φ (RetV 1)) -∗
      WP@{rs} (interp_expr (prog2 err) (λne (x : leibnizO ∅), match x with end) : IT) {{ Φ }}.
    Proof.
      iIntros "Hσ H▷".
      simpl.
      iApply (wp_catch_throw _ _ (Ret 3) idfun (λne x, IF x (Ret 1) (Ret 0)) with "Hσ").
      - simpl.
        rewrite laterO_map_Next /=.
        rewrite NATOP_Ret.
        by simpl.
      - simpl.
        iIntros "!>H£ Hσ".
        rewrite IF_True; last lia.
        iApply wp_val.
        iModIntro.
        iApply ("H▷" with "H£ Hσ").
    Qed.

    Example prog3 (err : exc) : expr ∅ :=
      (try 
         (if (
              throw err #3
            )
          then #1
          else #0)
       catch err => ($0) * #4  
      )%syn.
    
    Example wp_prog3 (err : exc) (σ : stateF ♯ IT) Φ :
      has_substate σ -∗
      ▷(£1 -∗ has_substate σ -∗ Φ (RetV 12)) -∗
      WP@{rs} (interp_expr (prog3 err) (λne (x : leibnizO ∅), match x with end) : IT) {{ Φ }}.
    Proof.
      iIntros "Hσ H▷".
      simpl.
      iApply (wp_catch_throw _ _ (Ret 3) (λne x, IF x (Ret 1) (Ret 0)) idfun with "Hσ").
      - by rewrite laterO_map_Next /= NATOP_Ret /=.
      - iIntros "!> H£ Hσ".
        iApply wp_val.
        by iApply ("H▷" with "H£ Hσ").
    Qed.

    Example prog4 (err1 err2 : exc) : expr ∅ :=
      (try
         try
            throw err1 #3
         catch err2 => ($0) + $0
       catch err1 => ($0) * $0
      )%syn.
  
    Example wp_prog4 (err1 err2 : exc) (Herr : err1 <> err2) (σ : stateF ♯ IT) Φ :
      has_substate σ -∗
      ▷(£1 -∗ has_substate σ -∗ Φ (RetV 9)) -∗
      WP@{rs} (interp_expr (prog4 err1 err2) (λne (x : leibnizO ∅), match x with end) : IT) {{ Φ }}.
    Proof.
      Opaque _REG.
      iIntros "Hσ H▷".
      simpl.
      iApply (wp_reg _ _ err1 _ idfun with "Hσ").
      { reflexivity. }
      iIntros "!> H£ Hσ".
      iApply (wp_reg _ _ _ _ (get_val _) with "Hσ").
      { reflexivity. }
      iIntros "!> H£' Hσ".
      iApply (wp_throw _ _ _ _ _ _ _ (get_val _) with "Hσ").
      3: change (?a :: ?b :: σ) with ([a] ++ b::σ); reflexivity.
      { constructor; first done. constructor. }
      { by rewrite laterO_map_Next /= NATOP_Ret /=. }
      iIntros "!> H£'' Hσ".
      iApply wp_val.
      iModIntro.
      iApply ("H▷" with "H£ Hσ").
    Qed.
      
  End Examples.
  
End interp.
#[global] Opaque INPUT OUTPUT_.
