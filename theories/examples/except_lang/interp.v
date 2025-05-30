From gitrees Require Import gitree lang_generic.
From iris.algebra Require Import list.
From gitrees.effects Require Export exceptions.
From gitrees.examples.except_lang Require Import lang typing.

Require Import Binding.Lib Binding.Set.

Import IF_nat.

Module interp (Errors : ExcSig).
  
  Module _TYP := Typing Errors.
  Import _TYP.
  Import _LANG.
  Import _Exc.

  Section interp.

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
      intros ??????? H.
      solve_proper_prepare.
      f_equiv.
      intros [| [| y']]; simpl; [done | apply H | done].      
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
      apply laterO_map_ne. intros a2; simpl.
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
      intros ?? K ? n x y Hxy a; simpl.
      repeat f_equiv; last done.
      intros b. simpl.
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
      apply laterO_map_ne.
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
          f_equiv; last done.
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
          f_equiv.
          * intro. done.
          * apply ne_proper; last done.
            solve_proper.
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
      interp_val (bind δ e) env ≡ interp_val e (sub_scope δ env).
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
      { simpl. destruct (eq_dec err err); done. }
      eapply Forall_impl.
      { exact Hfall. }
      intros [[err' ?] ?] ?.
      simpl.
      destruct (eq_dec err err'); done.
    Qed.
    
    Theorem soundness {S} : ∀ c c' e e' σr σ σ' n (env : interp_scope S),
      interp_config c env = (e, σ) → 
      interp_config c' env = (e', σ') → 
      c ===> c' / n →
      external_steps (gReifiers_sReifier rs)
        e (gState_recomp σr (sR_state σ))
        e' (gState_recomp σr (sR_state σ')) [] n.
    Proof.
      intros.
      revert H H0.
      inversion H1; intros HE0 HE1. 
      - simpl in HE0, HE1.
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; done.
      - simpl in HE0, HE1.
        rewrite HE0 in HE1.
        injection HE1 as <- <-.
        constructor; done.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [f t].
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; done.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [f t].
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; done.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [f t].
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; done.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [f t] eqn:Heq.
        assert (IT_hom f).
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        eapply reductions.steps_many with _ _ [] []; first reflexivity.
        + rewrite hom_vis.
          eapply (external_step_reify _ _ _ _ _ _ _ _ []); first done.
          rewrite (reify_vis_eq_ctx_dep _ _ _ _ _ _ _ []).
          { rewrite Tick_eq. done. }
          epose (@subReifier_reify _ _ _ _ _ _ _ (inl ()) ?[x] (Next _) ?[k] ?[t] ?[σ'] σr []) as Hry.
          match goal with
          | |- _ _ _ (_ ?x', (_ _ (_ ?σ2)) , ?k' ◎ _) ≡ _ =>  instantiate (x := x');
                                                              instantiate (k := k')
                                                                          
          end.
          Unshelve.
          5 : { simpl. done. }
          1 : { simpl in Hry|-*.
                erewrite <-Hry.
                - repeat f_equiv; first by solve_proper.
                  intro. simpl. done.
                - reflexivity.
          }
        + constructor.
          * repeat f_equiv.
            intro. simpl.
            do 2 f_equiv.
            intro.
            simpl.
            done.
          * simpl.
            do 5 f_equiv;
            f_equiv;
            intro;
            simpl;
            done.
          * reflexivity.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [f t] eqn:Heq.
        assert (IT_hom f).
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        by constructor.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [f t] eqn:Heq.
        assert (IT_hom f).
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        by constructor.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [g t] eqn:Heq.
        assert (IT_hom g) as Hg.
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        eapply reductions.steps_many with _ _ [] []; first done;
          last (econstructor; reflexivity).
        apply external_step_tick; last done.
        rewrite -hom_tick.
        f_equiv.
        pose (interp_rec_unfold (interp_expr f) env) as HEq.
        assert (∀ x y z : IT, x ≡ y → x ⊙ z ≡ y ⊙ z) as APP'_equiv.
        { intros x y z Hxy.
          Transparent APP APP'.
          simpl.
          Opaque APP APP'.
          repeat f_equiv.
          done.
        } 
        rewrite (APP'_equiv _ _ _ HEq) APP_APP'_ITV APP_Fun Tick_eq /=.
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
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [g t] eqn:Heq.
        assert (IT_hom g) as Hg.
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; last done; last done.
        f_equiv.
        destruct n0.
        + rewrite IF_False; last lia.
          done.
        + rewrite IF_True; last lia.
          done.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [g t] eqn:Heq.
        assert (IT_hom g) as Hg.
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; done.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [g t] eqn:Heq.
        assert (IT_hom g) as Hg.
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        constructor; last done; last done.
        f_equiv.
        destruct v1, v2.
        2, 3, 4 : contradict H; done.
        simpl in H.
        injection H as <-.
        simpl.
        apply NATOP_Ret.
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [g t] eqn:Heq.
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        eapply reductions.steps_many with _ _ [] []; first done;
          last (econstructor; reflexivity).
        rewrite get_val_ITV /= get_val_vis.
        eapply (external_step_reify); first done.
        rewrite (reify_vis_eq_ctx_dep _ _ _ _ _ _ _ []).
        { rewrite Tick_eq. done. }
        epose proof (@subReifier_reify _ _ _ _ _ _ _ (inr (inl ())) ?[x] (Next _) ?[k] ?[σ] ?[σ'] σr [] _) as Hry.
        match goal with
        | |- _ _ _ (_ ?x', (_ _ (_ (_ ?σ2) _)) , ?k1 ◎ (?k2 ◎ _)) ≡ _ =>
            instantiate (x := x');
            instantiate (k := k1 ◎ k2);
            instantiate (σ := σ2)
        end.
        Unshelve.
        4 : { simpl. destruct (eq_dec err) as [? | ?]; done. }
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
      - simpl in HE0, HE1.
        destruct (split_cont k env) as [g t] eqn:Heq.
        destruct (split_cont k' env) as [g' t'] eqn:Heq'.
        assert (IT_hom g) as Hg.
        { eapply split_cont_left_hom'. apply Heq. }
        injection HE0 as <- <-.
        injection HE1 as <- <-.
        eapply reductions.steps_many with _ _ [] []; first done;
          last (econstructor; reflexivity).
        rewrite get_val_ITV hom_vis.
        eapply (external_step_reify _ _ _ _ _ _ _ _ []); first done.
        rewrite (reify_vis_eq_ctx_dep _ _ _ _ _ _ _ []).
        { rewrite Tick_eq. done. }
        epose proof (@subReifier_reify _ _ _ _ _ _ _ (inr (inr (inl ()))) ?[x] (Next _) ?[k] ?[σ] t' σr [] _) as Hry.
        match goal with
        | |- _ _ _ (_ ?x', (_ _ (_ _ ?σ2)) , _) ≡ _ =>
            instantiate (x := x');
            instantiate (σ := σ2)
        end.
        Unshelve.
        4 : { Opaque cut_when. simpl. 
              apply (unwind_cut_when _ _ env _ _ _ _ _ _ Heq Heq') in H.
              rewrite H.             
              f_equiv. 
              rewrite laterO_map_Next.
              Opaque extend_scope.
              simpl.
              rewrite pair_equiv.
              split; last done.
              f_equiv.
        }
        1 : {
          simpl in Hry.
          simpl.
          rewrite interp_expr_subst /=.
          assert ((sub_scope (mk_subst (Val v)) env)
                    ≡ (extend_scope env (interp_val v env))) as ->.
          { intros [|]; simpl; done. }           
          rewrite -Hry.
          repeat f_equiv; first solve_proper.
          intro.
          simpl.
          instantiate (k := (laterO_map (λne y, g y)) ◎  (λne x, Empty_set_rect (λ _ : ∅, laterO IT) x)).
          simpl.
          done.
          Unshelve.
          intros n0 [].
        }
      - simpl in HE0, HE1.
        rewrite HE0 in HE1.
        injection HE1 as <- <-.
        constructor; done.
    Qed.

    End interp.
End interp.
