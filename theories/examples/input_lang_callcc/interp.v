From gitrees Require Import gitree lang_generic effects.io_tape.
From gitrees.examples.input_lang_callcc Require Import lang.
Require Import Binding.Lib Binding.Set.

Program Definition callccE : opInterp :=
  {|
    Ins := ((▶ ∙ -n> ▶ ∙) -n> ▶ ∙);
    Outs := (▶ ∙);
  |}.
Program Definition throwE : opInterp :=
  {|
    Ins := (▶ ∙ * (▶ (∙ -n> ∙)));
    Outs := Empty_setO;
  |}.

Definition contE := @[callccE;throwE].

Definition reify_callcc X `{Cofe X} : ((laterO X -n> laterO X) -n> laterO X) *
                                        unitO * (laterO X -n> laterO X) →
                                      option (laterO X * unitO) :=
  λ '(f, σ, k), Some ((k (f k): laterO X), σ : unitO).
#[export] Instance reify_callcc_ne X `{Cofe X} :
  NonExpansive (reify_callcc X :
    prodO (prodO ((laterO X -n> laterO X) -n> laterO X) unitO)
      (laterO X -n> laterO X) →
    optionO (prodO (laterO X) unitO)).
Proof. intros ?[[]][[]][[]]. simpl in *. repeat f_equiv; auto. Qed.

Definition reify_throw X `{Cofe X} :
  ((laterO X * (laterO (X -n> X))) * unitO * (Empty_setO -n> laterO X)) →
  option (laterO X * unitO) :=
  λ '((e, k'), σ, _),
    Some (((laterO_ap k' : laterO X -n> laterO X) e : laterO X), σ : unitO).
#[export] Instance reify_throw_ne X `{Cofe X} :
  NonExpansive (reify_throw X :
      prodO (prodO (prodO (laterO X) (laterO (X -n> X))) unitO)
        (Empty_setO -n> laterO X) →
    optionO (prodO (laterO X) (unitO))).
Proof.
  intros ?[[[]]][[[]]]?. rewrite /reify_throw.
  repeat f_equiv; apply H0.
Qed.

Canonical Structure reify_cont : sReifier CtxDep.
Proof.
  simple refine {| sReifier_ops := contE;
                   sReifier_state := unitO
                |}.
  intros X HX op.
  destruct op as [|[|[]]]; simpl.
  - simple refine (OfeMor (reify_callcc X)).
  - simple refine (OfeMor (reify_throw X)).
Defined.

Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff contE E}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Program Definition CALLCC_ : ((laterO IT -n> laterO IT) -n> laterO IT) -n>
                                (laterO IT -n> laterO IT) -n>
                                IT :=
    λne f k, Vis (E:=E) (subEff_opid (inl ()))
             (subEff_ins (F:=contE) (op:=(inl ())) f)
             (k ◎ (subEff_outs (F:=contE) (op:=(inl ())))^-1).
  Solve All Obligations with solve_proper.

  Program Definition CALLCC : ((laterO IT -n> laterO IT) -n> laterO IT) -n> IT :=
    λne f, CALLCC_ f (idfun).
  Solve Obligations with solve_proper.

  Lemma hom_CALLCC_ k e f `{!IT_hom f} :
    f (CALLCC_ e k) ≡ CALLCC_ e (laterO_map (OfeMor f) ◎ k).
  Proof.
    unfold CALLCC_.
    rewrite hom_vis/=.
    f_equiv. by intro.
  Qed.

  Program Definition THROW : IT -n> (laterO (IT -n> IT)) -n> IT :=
    λne e k, Vis (E:=E) (subEff_opid (inr (inl ())))
               (subEff_ins (F:=contE) (op:=(inr (inl ())))
                  (NextO e, k))
               (λne x, Empty_setO_rec _ ((subEff_outs (F:=contE) (op:=(inr (inl ()))))^-1 x)).
  Next Obligation.
    solve_proper_prepare.
    destruct ((subEff_outs ^-1) x).
  Qed.
  Next Obligation.
    intros; intros ???; simpl.
    repeat f_equiv. assumption.
  Qed.
  Next Obligation.
    intros ?????; simpl.
    repeat f_equiv; assumption.
  Qed.

End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
  Context {subR : subReifier reify_cont rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Implicit Type σ : unitO.
  Implicit Type κ : IT -n> IT.
  Implicit Type x : IT.

  Lemma wp_throw' σ κ (f : IT -n> IT) (x : IT)
    `{!IT_hom κ} Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} f x @ s {{ Φ }}) -∗
    WP@{rs} κ (THROW x (Next f)) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha". rewrite /THROW. simpl.
    rewrite hom_vis.
    iApply (wp_subreify_ctx_dep with "Hs"); simpl; done.
  Qed.

  Lemma wp_throw σ (f : IT -n> IT) (x : IT) Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} f x @ s {{ Φ }}) -∗
    WP@{rs} (THROW x (Next f)) @ s {{ Φ }}.
  Proof.
    iApply (wp_throw' _ idfun).
  Qed.

  Lemma wp_callcc σ (f : (laterO IT -n> laterO IT) -n> laterO IT) (k : IT -n> IT) {Hk : IT_hom k} β Φ s :
    f (laterO_map k) ≡ Next β →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k β @ s {{ Φ }}) -∗
    WP@{rs} (k (CALLCC f)) @ s {{ Φ }}.
  Proof.
    iIntros (Hp) "Hs Ha".
    unfold CALLCC. simpl.
    rewrite hom_vis.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ (laterO_map k (Next β))  with "Hs").
    {
      simpl. rewrite -Hp. repeat f_equiv; last done.
      rewrite ccompose_id_l. rewrite ofe_iso_21.
      repeat f_equiv. intro.
      simpl. f_equiv.
      apply ofe_iso_21.
    }
    {
      simpl. by rewrite later_map_Next.
    }
    iModIntro.
    iApply "Ha".
  Qed.

  (* XXX TODO: this duplicates wp_input and wp_output *)
  Context `{!subReifier (sReifier_NotCtxDep_CtxDep reify_io) rs}.
  Context `{!SubOfe natO R}.
  Lemma wp_input' (σ σ' : stateO) (n : nat) (k : natO -n> IT) (κ : IT -n> IT)
    `{!IT_hom κ} Φ s :
    update_input σ = (n, σ') ->
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} (κ ◎ k $ n) @ s {{ Φ }}) -∗
    WP@{rs} κ (INPUT k) @ s {{ Φ }}.
  Proof.
    iIntros (Hσ) "Hs Ha".
    rewrite hom_INPUT.
    iApply (wp_subreify_ctx_dep with "Hs").
    + simpl. rewrite Hσ. simpl. done.
    + by rewrite ofe_iso_21.
    + done.
  Qed.
  Lemma wp_output' (σ σ' : stateO) (n : nat) (κ : IT -n> IT)
     `{!IT_hom κ} Φ s :
    update_output n σ = σ' →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} (κ (Ret 0)) @ s {{ Φ }}) -∗
    WP@{rs} κ (OUTPUT n) @ s {{ Φ }}.
  Proof.
    iIntros (Hσ) "Hs Ha".
    rewrite /OUTPUT hom_OUTPUT_.
    iApply (wp_subreify_ctx_dep with "Hs").
    + simpl. by rewrite Hσ.
    + done.
    + done.
  Qed.

End weakestpre.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
  Context {subR1 : subReifier reify_cont rs}.
  Context {subR2 : subReifier (sReifier_NotCtxDep_CtxDep reify_io) rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Global Instance denot_cont_ne (κ : IT -n> IT) :
    NonExpansive (λ x : IT, Tau (laterO_map κ (Next x))).
  Proof.
    solve_proper.
  Qed.

  (** Interpreting individual operators *)
  Program Definition interp_input {A} : A -n> IT :=
    λne env, INPUT Ret.
  Program Definition interp_output {A} (t : A -n> IT) : A -n> IT :=
    get_ret OUTPUT ◎ t.
  Local Instance interp_ouput_ne {A} : NonExpansive2 (@interp_output A).
  Proof. solve_proper. Qed.

  Program Definition interp_callcc {S}
    (e : @interp_scope F R _ (inc S) -n> IT) : interp_scope S -n> IT :=
    λne env, CALLCC (λne (f : laterO IT -n> laterO IT),
                       (Next (e (@extend_scope F R _ _ env
                                   (Fun (Next (λne x, Tau (f (Next x))))))))).
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros [| a]; simpl; last solve_proper.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros [| a]; simpl; last solve_proper.
    repeat f_equiv.
  Qed.

  Program Definition interp_throw {A} (e : A -n> IT) (k : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne x, get_fun (λne (f : laterO (IT -n> IT)),
                                 THROW x f) (k env)) (e env).
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intro; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; last done.
    intro; simpl.
    by repeat f_equiv.
  Qed.

  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_natop.

  Opaque laterO_map.
  Program Definition interp_rec_pre {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT)
    : laterO (@interp_scope F R _ S -n> IT) -n> @interp_scope F R _ S -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : @interp_scope F R  _ S -n> IT) (a : IT),
                      body (@extend_scope F R _ _ (@extend_scope F R _ _ env (self env)) a)) self.
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
    (body : @interp_scope F R _ (inc (inc S)) -n> IT) :
    @interp_scope F R _ S -n> IT :=
    mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set}
    (body : @interp_scope F R _ (inc (inc S)) -n> IT) env : IT -n> IT :=
    λne a, body (@extend_scope F R _ _
                   (@extend_scope F R _ _ env (interp_rec body env))
                   a).
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv. intros [| [| y']]; simpl; solve_proper.
  Qed.

  Lemma interp_rec_unfold {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT) env :
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

  Program Definition interp_cont {A} (K : A -n> (IT -n> IT)) : A -n> IT :=
    λne env, (Fun (Next (λne x, Tau (laterO_map (K env) (Next x))))).
  Solve All Obligations with solve_proper_please.

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

  Program Definition interp_outputk {A} (K : A -n> (IT -n> IT)) :
    A -n> (IT -n> IT) :=
    λne env t, interp_output (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_throwlk {A} (K : A -n> (IT -n> IT)) (k : A -n> IT) :
    A -n> (IT -n> IT) :=
    λne env t, interp_throw (λne env, K env t) k env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_throwrk {A} (e : A -n> IT) (K : A -n> (IT -n> IT)) :
    A -n> (IT -n> IT) :=
    λne env t, interp_throw e (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | LitV n => interp_nat n
    | RecV e => interp_rec (interp_expr e)
    | ContV K => interp_cont (interp_ectx K)
    end
  with interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
         match e with
         | Val v => interp_val v
         | Var x => interp_var x
         | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
         | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
         | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
         | Input => interp_input
         | Output e => interp_output (interp_expr e)
         | Callcc e => interp_callcc (interp_expr e)
         | Throw e1 e2 => interp_throw (interp_expr e1) (interp_expr e2)
         end
  with interp_ectx {S} (K : ectx S) : interp_scope S -n> (IT -n> IT) :=
         match K with
         | EmptyK => λne env, idfun
         | AppRK e1 K => interp_apprk (interp_expr e1) (interp_ectx K)
         | AppLK K v2 => interp_applk (interp_ectx K) (interp_val v2)
         | NatOpRK op e1 K => interp_natoprk op (interp_expr e1) (interp_ectx K)
         | NatOpLK op K v2 => interp_natoplk op (interp_ectx K) (interp_val v2)
         | IfK K e1 e2 => interp_ifk (interp_ectx K) (interp_expr e1) (interp_expr e2)
         | OutputK K => interp_outputk (interp_ectx K)
         | ThrowLK K e => interp_throwlk (interp_ectx K) (interp_expr e)
         | ThrowRK v K => interp_throwrk (interp_val v) (interp_ectx K)
         end.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

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
      + repeat f_equiv.
        intros ?; simpl.
        repeat f_equiv.
        simpl; rewrite interp_expr_ren.
        f_equiv.
        intros [| y]; simpl.
        * reflexivity.
        * reflexivity.
      + repeat f_equiv.
        * intros ?; simpl.
          repeat f_equiv; first by apply interp_expr_ren.
        * by apply interp_expr_ren.
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
      + repeat f_equiv.
        intros ?; simpl.
        repeat f_equiv; by apply interp_ectx_ren.
    - destruct e; simpl; intros ?; simpl.
      + reflexivity.
      + repeat f_equiv; by apply interp_ectx_ren.
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_expr_ren | by apply interp_expr_ren].
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_val_ren].
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_ectx_ren].
      + repeat f_equiv; [by apply interp_expr_ren | by apply interp_ectx_ren].
      + repeat f_equiv; [by apply interp_ectx_ren | by apply interp_val_ren].
      + repeat f_equiv; last by apply interp_ectx_ren.
        intros ?; simpl; repeat f_equiv; by apply interp_expr_ren.
      + repeat f_equiv; last by apply interp_val_ren.
        intros ?; simpl; repeat f_equiv; first by apply interp_ectx_ren.
  Qed.

  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : ectx S):
    interp_expr (fill K e) env ≡ (interp_ectx K) env ((interp_expr e) env).
  Proof.
    revert env.
    induction K; simpl; intros env; first reflexivity; try (by rewrite IHK).
    - repeat f_equiv.
      by rewrite IHK.
    - repeat f_equiv.
      by rewrite IHK.
    - repeat f_equiv.
      by rewrite IHK.
    - repeat f_equiv.
      intros ?; simpl.
      repeat f_equiv.
      by rewrite IHK.
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
      + repeat f_equiv.
        intros ?; simpl.
        repeat f_equiv.
        rewrite interp_expr_subst.
        f_equiv.
        intros [| x']; simpl.
        * reflexivity.
        * rewrite interp_expr_ren.
          f_equiv.
          intros ?; reflexivity.
      + repeat f_equiv.
        * intros ?; simpl.
          repeat f_equiv; first by apply interp_expr_subst.
        * by apply interp_expr_subst.
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
      + repeat f_equiv; intro; simpl; repeat f_equiv.
        by apply interp_ectx_subst.
    - destruct e; simpl; intros ?; simpl.
      + reflexivity.
      + repeat f_equiv; by apply interp_ectx_subst.
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_expr_subst | by apply interp_expr_subst].
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_val_subst].
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_ectx_subst].
      + repeat f_equiv; [by apply interp_expr_subst | by apply interp_ectx_subst].
      + repeat f_equiv; [by apply interp_ectx_subst | by apply interp_val_subst].
      + repeat f_equiv; last by apply interp_ectx_subst.
        intros ?; simpl; repeat f_equiv; first by apply interp_expr_subst.
      + repeat f_equiv; last by apply interp_val_subst.
        intros ?; simpl; repeat f_equiv; first by apply interp_ectx_subst.
  Qed.

  (** ** Interpretation of evaluation contexts induces homomorphism *)

  #[local] Instance interp_ectx_hom_emp {S} env :
    IT_hom (interp_ectx (EmptyK : ectx S) env).
  Proof.
    simple refine (IT_HOM _ _ _ _ _); intros; auto.
    simpl. fold (@idfun IT). f_equiv. intro. simpl.
    by rewrite laterO_map_id.
  Qed.

  #[local] Instance interp_ectx_hom_output {S} (K : ectx S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (OutputK K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis.
      f_equiv. intro. simpl. rewrite -laterO_map_compose.
      do 2 f_equiv. by intro.
    - by rewrite !hom_err.
  Qed.

  #[local] Instance interp_ectx_hom_if {S}
    (K : ectx S) (e1 e2 : expr S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (IfK K e1 e2) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -IF_Tick. do 3 f_equiv. apply hom_tick.
    - assert ((interp_ectx K env (Vis op i ko)) ≡
        (Vis op i (laterO_map (λne y, interp_ectx K env y) ◎ ko))).
      { by rewrite hom_vis. }
      trans (IF (Vis op i (laterO_map (λne y : IT, interp_ectx K env y) ◎ ko))
               (interp_expr e1 env) (interp_expr e2 env)).
      { do 3 f_equiv. by rewrite hom_vis. }
      rewrite IF_Vis. f_equiv. simpl.
      intro. simpl. by rewrite -laterO_map_compose.
    - trans (IF (Err e) (interp_expr e1 env) (interp_expr e2 env)).
      { repeat f_equiv. apply hom_err. }
      apply IF_Err.
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
    - rewrite -APP'_Tick_l. do 2 f_equiv. apply hom_tick.
    - trans (APP' (Vis op i (laterO_map (interp_ectx K env) ◎ ko))
               (interp_val v env)).
      + do 2f_equiv. rewrite hom_vis. do 3 f_equiv. by intro.
      + rewrite APP'_Vis_l. f_equiv. intro x. simpl.
        by rewrite -laterO_map_compose.
    - trans (APP' (Err e) (interp_val v env)).
      { do 2f_equiv. apply hom_err. }
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
    - rewrite -NATOP_ITV_Tick_l. do 2 f_equiv. apply hom_tick.
    - trans (NATOP (do_natop op)
               (Vis op0 i (laterO_map (interp_ectx K env) ◎ ko))
               (interp_val v env)).
      { do 2 f_equiv. rewrite hom_vis. f_equiv. by intro. }
      rewrite NATOP_ITV_Vis_l. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - trans (NATOP (do_natop op) (Err e) (interp_val v env)).
      + do 2 f_equiv. apply hom_err.
      + by apply NATOP_Err_l, interp_val_asval.
  Qed.

  #[local] Instance interp_ectx_hom_throwr {S}
    (K : ectx S) (v : val S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (ThrowRK v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - pose proof (interp_val_asval v (D := env)).
      rewrite ->2 get_val_ITV.
      simpl.
      rewrite hom_tick.
      destruct (IT_dont_confuse ((interp_ectx K env α))) as [(e' & HEQ) |[(n & HEQ) |[(f & HEQ) |[(β & HEQ) | (op & i & k & HEQ)]]]].
      + rewrite HEQ !get_fun_tick !get_fun_err.
        reflexivity.
      + rewrite HEQ !get_fun_tick.
        reflexivity.
      + rewrite HEQ !get_fun_tick !get_fun_fun//=.
      + rewrite HEQ !get_fun_tick.
        reflexivity.
      + rewrite HEQ !get_fun_tick !get_fun_vis.
        reflexivity.
    - pose proof (interp_val_asval v (D := env)).
      rewrite get_val_ITV.
      simpl.
      rewrite hom_vis.
      rewrite get_fun_vis.
      f_equiv.
      intro; simpl.
      rewrite -laterO_map_compose.
      repeat f_equiv.
      intro; simpl.
      rewrite get_val_ITV.
      simpl.
      reflexivity.
    - pose proof (interp_val_asval v (D := env)).
      rewrite get_val_ITV.
      simpl.
      rewrite hom_err.
      rewrite get_fun_err.
      reflexivity.
  Qed.

  #[local] Instance interp_ectx_hom_throwl {S}
    (K : ectx S) (e : expr S) env :
    IT_hom (interp_ectx K env) ->
    IT_hom (interp_ectx (ThrowLK K e) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl; [by rewrite !hom_tick| | by rewrite !hom_err].
    rewrite !hom_vis.
    f_equiv.
    intro; simpl.
    rewrite -laterO_map_compose.
    reflexivity.
  Qed.

  #[global] Instance interp_ectx_hom {S}
    (K : ectx S) env :
    IT_hom (interp_ectx K env).
  Proof.
    induction K; apply _.
  Qed.

  (** ** Finally, preservation of reductions *)
  Lemma interp_expr_head_step {S : Set} (env : interp_scope S) (e : expr S) e' σ σ' K n :
    head_step e σ e' σ' K (n, 0) →
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

  Lemma interp_expr_fill_no_reify {S} K (env : interp_scope S) (e e' : expr S) σ σ' n :
    head_step e σ e' σ' K (n, 0) →
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

  Opaque INPUT OUTPUT_ CALLCC CALLCC_ THROW.
  Opaque extend_scope.
  Opaque Ret.

  Lemma interp_expr_fill_yes_reify {S} K env (e e' : expr S)
    (σ σ' : stateO) (σr : gState_rest sR_idx rs ♯ IT) n :
    head_step e σ e' σ' K (n, 1) →
    reify (gReifiers_sReifier rs)
      (interp_expr (fill K e) env) (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K e') env).
  Proof.
    intros Hst.
    trans (reify (gReifiers_sReifier rs) (interp_ectx K env (interp_expr e env))
             (gState_recomp σr (sR_state σ))).
    { f_equiv. by rewrite interp_comp. }
    inversion Hst; simplify_eq; cbn-[gState_recomp].
    - trans (reify (gReifiers_sReifier rs) (INPUT (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv; eauto.
        rewrite hom_INPUT.
        do 2 f_equiv. by intro.
      }
      rewrite reify_vis_eq_ctx_dep //; first last.
      {
        apply (subReifier_reify
                 (sReifier_NotCtxDep_CtxDep reify_io) rs (inl ())
                 () (Next (interp_ectx K env (Ret n0)))
                 (NextO ◎ (interp_ectx K env ◎ Ret)) σ σ' σr).
        simpl. rewrite H5. reflexivity.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
    - trans (reify (gReifiers_sReifier rs) (interp_ectx K env (OUTPUT n0)) (gState_recomp σr (sR_state σ))).
      {
        do 3 f_equiv; eauto.
        rewrite get_ret_ret//.
      }
      trans (reify (gReifiers_sReifier rs) (OUTPUT_ n0 (interp_ectx K env (Ret 0))) (gState_recomp σr (sR_state σ))).
      {
        do 2 f_equiv; eauto.
        by rewrite hom_OUTPUT_.
      }
      rewrite reify_vis_eq_ctx_dep //; last first.
      {
        simpl.
        pose proof (subReifier_reify
                 (sReifier_NotCtxDep_CtxDep reify_io) rs (inr (inl ()))
                 n0 (Next (interp_ectx K env (Ret 0)))
                 (constO (Next (interp_ectx K env ((Ret 0))))) σ (update_output n0 σ) σr) as H.
        simpl in H. erewrite <-H; last reflexivity.
        f_equiv.
        + do 3 intro. by rewrite /prod_map H0.
        + do 2 f_equiv. by intro.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
    - match goal with
      | |- context G [ofe_mor_car _ _ (CALLCC) ?g] => set (f := g)
      end.
      match goal with
      | |- context G [(?s, _)] => set (gσ := s) end.
      Transparent CALLCC.
      unfold CALLCC.
      simpl.
      trans (reify (gReifiers_sReifier rs) (CALLCC_ f (laterO_map (interp_ectx K env))) gσ).
      {
        do 2 f_equiv.
        rewrite hom_CALLCC_.
        f_equiv. by intro.
      }
      rewrite reify_vis_eq_ctx_dep//; last first.
      {
        simpl.
        set (ss := gState_decomp (@sR_idx _ _ _ _ subR1) gσ).
        pose (s1 := (sR_state^-1 ss.1)). simpl in s1.
        epose proof (subReifier_reify reify_cont rs (inl ()) f _
                       (laterO_map (interp_ectx K env))
                       s1 s1 (ss.2)) as H.
        simpl in H.
        erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. rewrite /prod_map H0. repeat f_equiv.
          rewrite ofe_iso_12.
          destruct ss; f_equiv; eauto. simpl.
          symmetry. apply ofe_iso_12.
        + repeat f_equiv; eauto.
          rewrite ofe_iso_12.
          destruct ss; f_equiv; eauto.
          symmetry. apply ofe_iso_12.
      }
      rewrite interp_comp.
      rewrite interp_expr_subst.
      f_equiv.
      { setoid_rewrite ofe_iso_12.
        by apply gState_recomp_decomp. }
      rewrite Tick_eq.
      f_equiv.
      rewrite laterO_map_Next.
      do 3 f_equiv.
      Transparent extend_scope.
      intros [| x]; term_simpl; last reflexivity.
      do 2 f_equiv. by intro.
  Qed.

  Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) :
    prim_step e1 σ1 e2 σ2 (n,m) →
    ssteps (gReifiers_sReifier rs)
              (interp_expr e1 env) (gState_recomp σr (sR_state σ1))
              (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n.
  Proof.
    Opaque gState_decomp gState_recomp.
    inversion 1; simplify_eq/=.
    {
      destruct (head_step_io_01 _ _ _ _ _ _ _ H2); subst.
      - assert (σ1 = σ2) as ->.
        { eapply head_step_no_io; eauto. }
        unshelve eapply (interp_expr_fill_no_reify K) in H2; first apply env.
        rewrite H2.
        rewrite interp_comp.
        eapply ssteps_tick_n.
      - inversion H2;subst.
        + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
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
        + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
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
        + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2.
          rewrite !interp_comp interp_expr_subst.
          change 1 with (Nat.add 1 0). econstructor; last first.
          { apply ssteps_zero; reflexivity. }
          rewrite -interp_comp.
          eapply sstep_reify.
          { Transparent CALLCC. unfold CALLCC. rewrite interp_comp hom_vis.
            f_equiv. reflexivity.
          }
          rewrite H2.
          simpl.
          repeat f_equiv.
          rewrite -interp_expr_subst.
          rewrite interp_comp.
          reflexivity.
    }
    {
      rewrite !interp_comp.
      simpl.
      pose proof (interp_val_asval v (D := env)).
      rewrite get_val_ITV.
      simpl.
      rewrite get_fun_fun.
      simpl.
      change 2 with (Nat.add (Nat.add 1 1) 0).
      econstructor; last first.
      { apply ssteps_tick_n. }
      eapply sstep_reify; first (rewrite hom_vis; reflexivity).
      match goal with
      | |- context G [ofe_mor_car _ _ _ (Next ?f)] => set (f' := f)
      end.
      trans (reify (gReifiers_sReifier rs) (THROW (interp_val v env) (Next f')) (gState_recomp σr (sR_state σ2))).
      {
        f_equiv; last done.
        f_equiv.
        rewrite hom_vis.
        Transparent THROW.
        unfold THROW.
        simpl.
        repeat f_equiv.
        intros x; simpl.
        destruct ((subEff_outs ^-1) x).
      }
      rewrite reify_vis_eq_ctx_dep; first (rewrite Tick_eq; reflexivity).
      simpl.
      match goal with
      | |- context G [(_, _, ?a)] => set (κ := a)
      end.
      set (gσ := (gState_recomp σr (sR_state (σ2 : sReifier_state (sReifier_NotCtxDep_CtxDep reify_io) ♯ IT)))).
      (* set (gσ := (gState_recomp σr (sR_state σ2))). *)
      set (ss := gState_decomp (@sR_idx _ _ _ _ subR1) gσ).
      pose (s1 := (sR_state^-1 ss.1)). simpl in gσ, s1.
      epose proof (subReifier_reify reify_cont rs (inr (inl ()))
                    (Next (interp_val v env), Next f')
                     (Next (Tau (Next ((interp_ectx K' env) (interp_val v env)))))
                     (Empty_setO_rec _) s1 s1 ss.2) as H'.
      simpl in H'.
      subst κ.
      simpl. trans (Some
             (Next (Tau (Next (interp_ectx K' env (interp_val v env)))),
               gState_recomp ss.2 (sR_state (s1 : sReifier_state reify_cont ♯ IT)))).
      - erewrite <-H'; last reflexivity.
        rewrite /prod_map.
        f_equiv.
        + repeat intro. repeat f_equiv; eauto.
          unfold s1.
          setoid_rewrite ofe_iso_12.
          symmetry. by apply gState_recomp_decomp.
        + do 2 f_equiv.
          * repeat f_equiv. unfold s1.
            setoid_rewrite ofe_iso_12.
            symmetry. by apply gState_recomp_decomp.
          * intro; simpl.
            f_equiv. done.
      - rewrite Tick_eq. repeat f_equiv.
        unfold s1.
        setoid_rewrite ofe_iso_12.
        by apply gState_recomp_decomp. }
  Qed.

End interp.
#[global] Opaque INPUT OUTPUT_ CALLCC THROW.
