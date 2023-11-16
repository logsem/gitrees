From Equations Require Import Equations.
From gitrees Require Import gitree.
From gitrees.input_lang_callcc Require Import lang.
Require Import gitrees.lang_generic_sem.

Require Import Binding.Lib.
Require Import Binding.Set.

Notation stateO := (leibnizO state).

Program Definition inputE : opInterp := {|
                                         Ins := unitO;
                                         Outs := natO;
                                       |}.
Program Definition outputE : opInterp := {|
                                          Ins := natO;
                                          Outs := unitO;
                                        |}.

Program Definition callccE : opInterp :=  {|
                                          Ins := ((▶ ∙ -n> ▶ ∙) -n> ▶ ∙);
                                          Outs := (▶ ∙);
                                        |}.

Program Definition throwE : opInterp :=  {|
                                         Ins := (▶ ∙ * (▶ (∙ -n> ∙)));
                                         Outs := unitO;
                                       |}.

Definition ioE := @[inputE;outputE;callccE;throwE].

Canonical Structure reify_io : sReifier.
Proof.
  simple refine {| sReifier_ops := ioE;
                   sReifier_state := stateO
                |}.
  intros X HX op.
  destruct op as [ | [ | [ | [| []]]]]; simpl.
  - simple refine (λne (us : prodO (prodO unitO stateO) (natO -n> laterO X)),
        let a : (prodO natO stateO) := (update_input (sndO (fstO us))) in
       Some $ ((sndO us) (fstO a), sndO a) : optionO (prodO (laterO X) stateO)).
    intros n [[] s1] [[] s2] [[Hs1 Hs2] Hs]; simpl in *.
    repeat f_equiv; assumption.
  - simple refine (λne (us : prodO (prodO natO stateO) (unitO -n> laterO X)),
        let a : stateO := update_output (fstO (fstO us)) (sndO (fstO us)) in
        Some $ ((sndO us) (), a) : optionO (prodO (laterO X) stateO)).
    intros n [[t1 t2] s1] [[y1 y2] s2] [Hs' Hs]. simpl in *.
    repeat f_equiv.
    + apply Hs.
    + apply Hs'.
    + apply Hs'.
  - simple refine (λne (us : prodO (prodO ((laterO X -n> laterO X) -n> laterO X) stateO) (laterO X -n> laterO X)), Some $ ((fstO (fstO us)) (sndO us), sndO (fstO us))).
    solve_proper.
  - simple refine (λne (us : prodO (prodO (prodO (laterO X) (laterO (X -n> X))) stateO) (unitO -n> laterO X)), Some (laterO_ap us.1.1.2 us.1.1.1, sndO (fstO us))).
    intros ????.
    repeat f_equiv; assumption.
Defined.

Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff ioE E}.
  Context {subOfe0 : SubOfe natO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Program Definition CALLCC : ((laterO IT -n> laterO IT) -n> laterO IT) -n> (laterO IT -n> laterO IT) -n> IT :=
    λne e k, Vis (E:=E) (subEff_opid (inr (inr (inl ()))))
               (subEff_ins (F:=ioE) (op:=(inr (inr (inl ())))) e)
               (λne o, (k ((subEff_outs (F:=ioE) (op:=(inr (inr (inl ())))))^-1 o))).
  Next Obligation.
    intros.
    intros ???.
    by do 2 f_equiv.
  Qed.
  Next Obligation.
    intros.
    intros ???.
    f_equiv.
    intros ?; simpl.
    by do 1 f_equiv.
  Qed.
  Next Obligation.
    intros ?????; simpl.
    by do 2 f_equiv.
  Qed.

  Lemma hom_CALLCC e k f `{!IT_hom f} : f (CALLCC e k) ≡ CALLCC e (laterO_map (OfeMor f) ◎ k).
  Proof.
    unfold CALLCC.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map].
    f_equiv.
  Qed.

  Program Definition INPUT : (nat -n> IT) -n> IT := λne k, Vis (E:=E) (subEff_opid (inl ()))
                                                             (subEff_ins (F:=ioE) (op:=(inl ())) ())
                                                             (NextO ◎ k ◎ (subEff_outs (F:=ioE) (op:=(inl ())))^-1).
  Solve Obligations with solve_proper.
  Program Definition OUTPUT_ : nat -n> IT -n> IT :=
    λne m α, Vis (E:=E) (subEff_opid (inr (inl ())))
                        (subEff_ins (F:=ioE) (op:=(inr (inl ()))) m)
                        (λne _, NextO α).
  Solve All Obligations with solve_proper_please.
  Program Definition OUTPUT : nat -n> IT := λne m, OUTPUT_ m (Ret 0).

  Lemma hom_INPUT k f `{!IT_hom f} : f (INPUT k) ≡ INPUT (OfeMor f ◎ k).
  Proof.
    unfold INPUT.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map]. rewrite laterO_map_Next.
    done.
  Qed.
  Lemma hom_OUTPUT_ m α f `{!IT_hom f} : f (OUTPUT_ m α) ≡ OUTPUT_ m (f α).
  Proof.
    unfold OUTPUT.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map]. rewrite laterO_map_Next.
    done.
  Qed.

  Program Definition THROW : IT -n> (laterO (IT -n> IT)) -n> IT :=
    λne m α, Vis (E:=E) (subEff_opid (inr (inr (inr (inl ())))))
                        (subEff_ins (F:=ioE) (op:=(inr (inr (inr (inl ()))))) (NextO m, α))
                        (λne _, laterO_ap α (NextO m)).
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros; intros ???; simpl.
    repeat f_equiv; [assumption |].
    intros ?; simpl.
    apply Next_contractive.
    destruct n as [| n].
    - apply dist_later_0.
    - apply dist_later_S.
      apply dist_later_S in H.
      apply H.
  Qed.
  Next Obligation.
    intros ?????; simpl.
    repeat f_equiv; [assumption |].
    intros ?; simpl.
    repeat f_equiv; assumption.
  Qed.

End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_input (σ σ' : stateO) (n : nat) (k : natO -n> IT) Φ s :
    update_input σ = (n, σ') →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} (k n) @ s {{ Φ }}) -∗
    WP@{rs} (INPUT k) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold INPUT. simpl.
    iApply (wp_subreify with "Hs").
    { simpl. by rewrite Hs. }
    { simpl. by rewrite ofe_iso_21. }
    iModIntro. done.
  Qed.

  Lemma wp_output (σ σ' : stateO) (n : nat) Φ s :
    update_output n σ = σ' →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ Φ (RetV 0)) -∗
    WP@{rs} (OUTPUT n) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold OUTPUT. simpl.
    iApply (wp_subreify with "Hs").
    { simpl. by rewrite Hs. }
    { simpl. done. }
    iModIntro. iIntros "H1 H2".
    iApply wp_val. by iApply ("Ha" with "H1 H2").
    Unshelve.
    simpl; constructor.
  Qed.

  (* wp_subreify *)
  (* Lemma wp_callcc (σ : stateO) (e : (laterO IT -n> laterO IT) -n> laterO IT) (k : laterO IT -n> laterO IT) Φ s : *)
  (*   has_substate σ -∗ *)
  (*   ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} (later_car (k (e k))) @ s {{ Φ }}) -∗ *)
  (*   WP@{rs} (CALLCC e k) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hs Ha". *)
  (*   unfold CALLCC. simpl. *)
  (*   iApply (wp_subreify with "Hs"). *)
  (*   { *)
  (*     simpl. *)
  (*     do 2 f_equiv; last reflexivity. *)
  (*     Unshelve. *)
  (*     3: apply (k (e k)). *)
  (*     2: simpl; apply (e k). *)
  (*     simpl. *)
  (*     rewrite ofe_iso_21. *)
  (*     admit. *)
  (*   } *)
  (*   { *)
  (*     simpl. *)
  (*     rewrite ofe_iso_21. *)
  (*     f_equiv. *)
  (*   } *)
  (*   iModIntro. *)
  (*   iApply "Ha". *)
  (* Admitted. *)

  Lemma wp_throw (σ : stateO) (f : laterO (IT -n> IT)) (x : IT) Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} later_car f x @ s {{ Φ }}) -∗
    WP@{rs} (THROW x f) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold THROW. simpl.
    iApply (wp_subreify with "Hs").
    {
      simpl.
      do 2 f_equiv; reflexivity.
    }
    {
      simpl.
      reflexivity.
    }
    iModIntro.
    iApply "Ha".
    Unshelve.
    simpl.
    constructor.
  Qed.

End weakestpre.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_io rs}.
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context {subEff0 : subEff ioE F}.

  (** Interpreting individual operators *)
  Program Definition interp_input {A} : A -n> (IT -n> IT) -n> IT :=
    λne env κ, κ (INPUT Ret).
  Solve All Obligations with solve_proper.

  Program Definition interp_output {A} (t : A -n> (IT -n> IT) -n> IT) : A -n> (IT -n> IT) -n> IT :=
    λne env κ, t env (λne x, κ ((get_ret OUTPUT x))).
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.

  Program Definition interp_callcc {S} (e : @interp_scope F R _ (inc S) -n> (IT -n> IT) -n> IT)
    : interp_scope S -n> (IT -n> IT) -n> IT := λne env κ, CALLCC (λne (f : laterO IT -n> laterO IT), f (Next (e (@extend_scope F R _ _ env (Fun (Next κ))) κ))) (laterO_ap (Next κ)).
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros; intros ???.
    repeat f_equiv.
    - intros a; simpl.
      repeat f_equiv; [| assumption].
      intros [| ?]; simpl; solve_proper.
    - assumption.
  Qed.
  Next Obligation.
    intros; intros ????; simpl.
    repeat f_equiv; intros ?; simpl.
    repeat f_equiv.
    intros [| ?]; simpl; solve_proper.
  Qed.

  Program Definition interp_throw {A} (n : A -n> (IT -n> IT) -n> IT) (m : A -n> (IT -n> IT) -n> IT)
    : A -n> (IT -n> IT) -n> IT := λne env κ, n env (λne n', m env (λne m', get_fun (λne (f : laterO (IT -n> IT)), THROW n' f) m')).
  Next Obligation.
    intros ???????????.
    f_equiv; assumption.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; last done.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  Global Instance interp_throw_ne A : NonExpansive2 (@interp_throw A).
  Proof.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    repeat f_equiv; first done.
  Qed.
  Typeclasses Opaque interp_throw.

  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> (IT -n> IT) -n> IT) : A -n> (IT -n> IT) -n> IT :=
    λne env κ, (t1 env (λne n, t2 env (λne m, κ (NATOP (do_natop op) n m)))).
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Typeclasses Opaque interp_natop.

  Opaque laterO_map.

  Program Definition interp_app {A} (t1 t2 : A -n> (IT -n> IT) -n> IT) : A -n> (IT -n> IT) -n> IT :=
    λne env κ, t1 env (λne m, t2 env (λne n, κ (APP' m n))).
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper_please.
  Qed.
  Next Obligation.
    intros; intros ???.
    f_equiv; intros ?; simpl.
    f_equiv; intros ?; simpl.
    by f_equiv.
  Qed.
  Next Obligation.
    solve_proper_please.
  Qed.

  Typeclasses Opaque interp_app.

  Program Definition interp_if {A} (t0 t1 t2 : A -n> (IT -n> IT) -n> IT) : A -n> (IT -n> IT) -n> IT :=
    λne env κ, (t0 env (λne b, (IF b (t1 env κ) (t2 env κ)))).
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    f_equiv.
    intros ?; simpl; solve_proper.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof.
    solve_proper_prepare.
    repeat f_equiv; first solve_proper.
    intros ?; simpl.
    repeat f_equiv; solve_proper.
  Qed.

  Program Definition interp_nat (n : nat) {A} : A -n> (IT -n> IT) -n> IT :=
    λne env κ, κ (Ret n).
  Solve All Obligations with solve_proper.

  Program Definition interp_var' {S : Set} (v : S) : interp_scope S -n> (IT -n> IT) -n> IT :=
    λne (f : interp_scope S) κ, κ (interp_var v f).
  Solve All Obligations with solve_proper.

  Program Definition interp_emptyk {A} : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT) := λne φ env κ, φ env κ.
  Solve All Obligations with try solve_proper.

  Program Definition interp_outputk {A} (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)) : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT) := λne φ env κ, interp_output (K φ) env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.

  Program Definition interp_ifk {A} (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    (q : A -n> (IT -n> IT) -n> IT)
    (p : A -n> (IT -n> IT) -n> IT)
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_if (K φ) q p env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.

  Program Definition interp_applk {A} (q : A -n> (IT -n> IT) -n> IT)
    (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_app q (K φ) env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  Program Definition interp_apprk {A} (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    (q : A -n> (IT -n> IT) -n> IT)
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_app (K φ) q env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.

  Program Definition interp_natoplk {A} (op : nat_op)
    (q : A -n> (IT -n> IT) -n> IT)
    (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_natop op q (K φ) env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  Program Definition interp_natoprk {A} (op : nat_op)
    (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    (q : A -n> (IT -n> IT) -n> IT)
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_natop op (K φ) q env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.

  Program Definition interp_throwlk {A}
    (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    (q : A -n> (IT -n> IT) -n> IT)
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_throw (K φ) q env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    by repeat f_equiv.
  Qed.

  Program Definition interp_throwrk {A}
    (q : A -n> (IT -n> IT) -n> IT)
    (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT)
    := λne φ env κ, interp_throw q (K φ) env κ.
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv; first done.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  (* Wrong *)
  Program Definition interp_rec_pre {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> (IT -n> IT) -n> IT)
    : laterO (@interp_scope F R _ S -n> (IT -n> IT) -n> IT) -n> @interp_scope F R _ S -n> (IT -n> IT) -n> IT :=
    λne self env κ,
      κ (Fun $ laterO_map (λne
                             (self : @interp_scope F R  _ S -n> (IT -n> IT) -n> IT)
                             (a : IT),
             body
               (@extend_scope F R _ _ (@extend_scope F R _ _ env (self env κ)) a)
               κ
           ) self).
  Next Obligation.
    intros.
    solve_proper_prepare.
    do 2 f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    do 2 f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv; [assumption |].
    do 3 f_equiv; intros ??; simpl; f_equiv.
    - f_equiv; intros [| [| y']]; simpl; solve_proper.
    - assumption.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    do 4 f_equiv; intros ??; simpl.
    do 2 f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    by do 3 f_equiv.
  Qed.

  Program Definition interp_rec {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> (IT -n> IT) -n> IT) : @interp_scope F R _ S -n> (IT -n> IT) -n> IT := mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> (IT -n> IT) -n> IT) env κ : IT -n> IT :=
    λne a, body (@extend_scope F R _ _ (@extend_scope F R _ _ env (interp_rec body env κ)) a) κ.
  Next Obligation.
    intros.
    solve_proper_prepare.
    repeat f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.

  Lemma interp_rec_unfold {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> (IT -n> IT) -n> IT) env κ :
    interp_rec body env κ ≡ κ $ Fun $ Next $ ir_unf body env κ.
  Proof.
    trans (interp_rec_pre body (Next (interp_rec body)) env κ).
    { do 2 f_equiv. rewrite /interp_rec. apply mmuu_unfold. }
    simpl. rewrite laterO_map_Next. repeat f_equiv.
    simpl. unfold ir_unf. simpl.
    intro. simpl. reflexivity.
  Qed.

  (* Wrong *)
  Program Definition interp_cont {A}
    (K : (A -n> (IT -n> IT) -n> IT) -n> (A -n> (IT -n> IT) -n> IT))
    : A -n> (IT -n> IT) -n> IT
    := λne env κ, Fun (Next (λne e, K (λne _ _, e) env κ)).
  Solve All Obligations with try solve_proper.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    by intros ??; simpl.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> (IT -n> IT) -n> IT :=
    match v with
    | LitV n => interp_nat n
    | VarV x => interp_var' x
    | RecV e => interp_rec (interp_expr e)
    | ContV K => interp_cont (interp_ectx K)
    end
  with interp_expr {S} (e : expr S) : interp_scope S -n> (IT -n> IT) -n> IT :=
         match e with
         | Val v => interp_val v
         | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
         | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
         | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
         | Input => interp_input
         | Output e => interp_output (interp_expr e)
         | Callcc e => interp_callcc (interp_expr e)
         | Throw e1 e2 => interp_throw (interp_expr e1) (interp_expr e2)
         end
  with interp_ectx {S} (K : ectx S) : (interp_scope S -n> (IT -n> IT) -n> IT) -n> (interp_scope S -n> (IT -n> IT) -n> IT) :=
         match K with
         | EmptyK => interp_emptyk
         | AppLK e1 K => interp_applk (interp_expr e1) (interp_ectx K)
         | AppRK K v2 => interp_apprk (interp_ectx K) (interp_val v2)
         | NatOpLK op e1 K => interp_natoplk op (interp_expr e1) (interp_ectx K)
         | NatOpRK op K v2 => interp_natoprk op (interp_ectx K) (interp_val v2)
         | IfK K e1 e2 => interp_ifk (interp_ectx K) (interp_expr e1) (interp_expr e2)
         | OutputK K => interp_outputk (interp_ectx K)
         | ThrowLK K e => interp_throwlk (interp_ectx K) (interp_expr e)
         | ThrowRK v K => interp_throwrk (interp_val v) (interp_ectx K)
         end.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

  #[global] Instance interp_val_asval {S} (v : val S) (D : interp_scope S)
   (H : ∀ (x : S), AsVal (D x))
    : AsVal (interp_val v D idfun).
  Proof.
    destruct v; simpl.
    - apply H.
    - apply _.
    - rewrite interp_rec_unfold. apply _.
    - apply _.
  Qed.

  Lemma interp_expr_ren {S S'} env env' κ
    (δ : S [→] S') (H : env' ≡ (ren_scope δ env)) e :
    interp_expr (fmap δ e) env κ ≡ interp_expr e env' κ
  with interp_val_ren {S S'} env env' κ
    (δ : S [→] S') (H : env' ≡ (ren_scope δ env)) e :
    interp_val (fmap δ e) env κ ≡ interp_val e env' κ
  with interp_ectx_ren {S S'} env env' κ φ φ'
    (δ : S [→] S') (H : env' ≡ (ren_scope δ env)) e :
    interp_ectx (fmap δ e) φ env κ ≡ interp_ectx e φ' env' κ.
  Proof.
    - destruct e; simpl.
      + by apply interp_val_ren.
      + f_equiv.
        * intros ?; by apply interp_expr_ren.
        * intros ?; simpl; by apply interp_expr_ren.
      + repeat f_equiv.
        * intros ?; simpl; by apply interp_expr_ren.
        * intros ?; simpl; by apply interp_expr_ren.
      + repeat f_equiv.
        * intros ?; by apply interp_expr_ren.
        * intros ?; simpl.
          repeat f_equiv.
          -- intros ?; simpl; by apply interp_expr_ren.
          -- intros ?; simpl; by apply interp_expr_ren.
      + f_equiv.
      + repeat f_equiv.
        intros ?; simpl; by apply interp_expr_ren.
      + repeat f_equiv.
        intros ?; simpl.
        repeat f_equiv.
        intros ?; simpl; apply interp_expr_ren.
        intros [| y]; simpl.
        * reflexivity.
        * specialize (H y).
          apply H.
      + repeat f_equiv.
        * intros ?; simpl.
          repeat f_equiv.
          intros ?; simpl; by apply interp_expr_ren.
        * intros ?; simpl; by apply interp_expr_ren.
    - destruct e; simpl.
      + f_equiv.
        rewrite (H _).
        reflexivity.
      + reflexivity.
      + clear -interp_expr_ren H.
        apply bi.siProp.internal_eq_soundness.
        iAssert (∀ (S S' : Set) (env : interp_scope S') (env' : interp_scope S) (κ : IT -n> IT) (δ : S [→] S'),
                   env' ≡ ren_scope δ env -∗ ∀ e : expr S, interp_expr (fmap δ e) env κ ≡ interp_expr e env' κ)%I as "H".
        {
          iIntros (? ? ? ? ? ?) "G".
          iIntros (?).
          iRewrite "G".
          iPureIntro.
          apply interp_expr_ren.
          reflexivity.
        }
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 2 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        unshelve iApply ("H" $! (inc (inc S)) (inc (inc S')) _ _ κ _ with "[H]").
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done.
        * by iRewrite - "IH".
        * by rewrite (H _).
      + repeat f_equiv.
        intros ?; simpl; by apply interp_ectx_ren.
    - admit.
  Admitted.

  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : ectx S) κ :
    interp_expr (fill K e) env κ ≡ (interp_ectx K) (interp_expr e) env κ.
  Proof.
    revert env.
    revert κ.
    induction K; simpl; intros κ env; first reflexivity; try (by rewrite IHK).
    - f_equiv.
      intros ?; simpl.
      by rewrite IHK.
    - f_equiv.
      intros ?; simpl.
      by rewrite IHK.
    - f_equiv.
      intros ?; simpl.
      by rewrite IHK.
  Qed.

  (* Lemma interp_val_push {S} v (env : interp_scope S) κ: *)
  (*   interp_val v env κ ≡ κ (interp_val v env idfun) *)
  (* (* with interp_ectx_push {S} k (env : interp_scope S) κ: *) *)
  (* (*   (λit e : IT, interp_ectx k env κ e) ≡ (κ (λit e : IT, interp_ectx k env idfun e)) *). *)
  (* Proof. *)
  (*   { *)
  (*     destruct v. *)
  (*     - reflexivity. *)
  (*     - reflexivity. *)
  (*     - simpl. *)
  (*       rewrite !interp_rec_unfold. *)
  (*       f_equiv. *)
  (*       simpl. *)
  (*       repeat f_equiv. *)
  (*       admit. *)
  (*     - simpl. *)
  (*       apply interp_ectx_push. *)

  (* Wrong *)
  (* Program Definition sub_scope {S S'} (δ : S [⇒] S') (env : interp_scope S') *)
  (*   : interp_scope S := λne x, interp_val (δ x) env idfun. *)

  (* Lemma interp_expr_subst {S S'} (env : interp_scope S') (env' : interp_scope S) κ *)
  (*   (δ : S [⇒] S') (H : env' ≡ sub_scope δ env) e : *)
  (*   interp_expr (bind δ e) env κ ≡ interp_expr e env' κ *)
  (* with interp_val_subst {S S'} (env : interp_scope S') (env' : interp_scope S) κ *)
  (*        (δ : S [⇒] S') (H : env' ≡ sub_scope δ env) e : *)
  (*   interp_val (bind δ e) env κ ≡ interp_val e env' κ *)
  (* with interp_ectx_subst {S S'} (env : interp_scope S') (env' : interp_scope S) κ φ φ' *)
  (*        (δ : S [⇒] S') (H : env' ≡ sub_scope δ env) e : *)
  (*   interp_ectx (bind δ e) φ env κ ≡ interp_ectx e φ' env' κ. *)
  (* Proof. *)
  (*   - destruct e; simpl. *)
  (*     + by apply interp_val_subst. *)
  (*     + f_equiv. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*     + f_equiv. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*     + f_equiv. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*       * intros ?; simpl. *)
  (*         f_equiv. *)
  (*         -- f_equiv; by apply interp_expr_subst. *)
  (*         -- by apply interp_expr_subst. *)
  (*     + f_equiv. *)
  (*     + f_equiv. *)
  (*       intros ?; simpl; by apply interp_expr_subst. *)
  (*     + repeat f_equiv. *)
  (*       intros ?; simpl. *)
  (*       repeat f_equiv. *)
  (*       intros ?; simpl; apply interp_expr_subst. *)
  (*       intros [| x']; simpl. *)
  (*       * reflexivity. *)
  (*       * rewrite interp_val_ren. *)
  (*         -- rewrite (H _). *)
  (*            simpl. *)
  (*            reflexivity. *)
  (*         -- intros ?; by term_simpl. *)
  (*     + repeat f_equiv. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*       * intros ?; simpl; by apply interp_expr_subst. *)
  (*   - destruct e; simpl. *)
  (*     + term_simpl. *)
  (*       rewrite (H _). *)
  (*       simpl. *)
  (*       admit. *)
  (*     + reflexivity. *)
  (*     + clear -interp_expr_subst H. *)
  (*       apply bi.siProp.internal_eq_soundness. *)
  (*       iAssert (∀ (S S' : Set) (env : interp_scope S') (env' : interp_scope S) (κ : IT -n> IT) (δ : S [⇒] S'), *)
  (*                  (env' ≡ sub_scope δ env) -∗ ∀ e : expr S, interp_expr (bind δ e) env κ ≡ interp_expr e env' κ)%I as "H". *)
  (*       { *)
  (*         iIntros (? ? ? ? ? ?) "G". *)
  (*         iIntros (?). *)
  (*         iRewrite "G". *)
  (*         iPureIntro. *)
  (*         apply interp_expr_subst. *)
  (*         reflexivity. *)
  (*       } *)
  (*       iLöb as "IH". *)
  (*       rewrite {2}interp_rec_unfold. *)
  (*       rewrite {2}(interp_rec_unfold (interp_expr e)). *)
  (*       do 2 iApply f_equivI. iNext. *)
  (*       iApply internal_eq_pointwise. *)
  (*       rewrite /ir_unf. iIntros (x). simpl. *)
  (*       unshelve iApply ("H" $! (inc (inc S)) (inc (inc S')) _ _ κ _ with "[H]").         *)
  (*       iApply internal_eq_pointwise. *)
  (*       iIntros (y'). *)
  (*       destruct y' as [| [| y]]; simpl; first done. *)
  (*       * by iRewrite - "IH". *)
  (*       * rewrite (H _). *)
  (*         simpl. *)
  (*         rewrite interp_val_ren. *)
  (*         2: reflexivity. *)
  (*         { *)
  (*           rewrite interp_val_ren. *)
  (*           - iPureIntro. reflexivity. *)
  (*           - intros z; simpl. *)
  (*             reflexivity. *)
  (*         } *)
  (*     + repeat f_equiv. *)
  (*       intros ?; simpl. *)
  (*       by apply interp_ectx_subst.         *)
  (*   - admit. *)
  (* Admitted. *)

  (** ** Finally, preservation of reductions *)
  Lemma interp_expr_head_step {S} env (e : expr S) e' σ σ' K n κ :
    head_step e σ e' σ' K (n, 0) →
    interp_expr e env κ ≡ Tick_n n $ interp_expr e' env κ.
  Proof.
    inversion 1; cbn-[IF APP' INPUT Tick get_ret2].
    - (* app lemma *)
      subst.
      admit.
      (* rewrite !interp_expr_subst; [| reflexivity | reflexivity]. *)
      (* trans (APP (Fun (Next (ir_unf (interp_expr e1) env κ))) (Next $ interp_val v2 env κ)). *)
      (* + rewrite interp_rec_unfold. *)
      (*   simpl. *)
      (*   admit. *)
      (* + rewrite APP_Fun. simpl. rewrite Tick_eq. do 4 f_equiv. *)
      (*   intros [| [| x]]; term_simpl. *)
      (*   * rewrite interp_val_ren. *)
      (*     -- admit. *)
      (*     -- reflexivity. *)
      (*   * admit. *)
      (*   * reflexivity. *)
    - (* the natop stuff *)
      simplify_eq.
      destruct v1,v2; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
    - subst.
      rewrite IF_True; last lia.
      reflexivity.
    - subst.
      rewrite IF_False; last lia.
      reflexivity.
    - subst.
      admit.
  Admitted.

  (* Lemma interp_expr_fill_no_reify {S} K env (e e' : expr S) σ σ' K n : *)
  (*   head_step e σ e' σ' K (n, 0) → *)
  (*   interp_expr (fill K e) env ≡ Tick_n n $ interp_expr (fill K e') env. *)
  (* Proof. *)
  (*   intros He. *)
  (*   trans (interp_ectx K env (interp_expr e env)). *)
  (*   { apply interp_ectx_fill. } *)
  (*   trans (interp_ectx K env (Tick_n n (interp_expr e' env))). *)
  (*   {  f_equiv. apply (interp_expr_head_step env) in He. apply He. } *)
  (*   trans (Tick_n n $ interp_ectx K env (interp_expr e' env)); last first. *)
  (*   { f_equiv. symmetry. apply interp_ectx_fill. } *)
  (*   apply hom_tick_n. apply _. *)
  (* Qed. *)

  (* Opaque INPUT OUTPUT_. *)
  (* Opaque Ret. *)

  (* Lemma interp_expr_fill_yes_reify {S} K env (e e' : expr S) *)
  (*   (σ σ' : stateO) (σr : gState_rest sR_idx rs ♯ IT) n : *)
  (*   head_step e σ e' σ' (n,1) → *)
  (*   reify (gReifiers_sReifier rs) *)
  (*     (interp_expr (fill K e) env)  (gState_recomp σr (sR_state σ)) *)
  (*     ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K e') env). *)
  (* Proof. *)
  (*   intros Hst. *)
  (*   trans (reify (gReifiers_sReifier rs) (interp_ectx K env (interp_expr e env)) *)
  (*            (gState_recomp σr (sR_state σ))). *)
  (*   { f_equiv. by rewrite interp_ectx_fill. } *)
  (*   inversion Hst; simplify_eq; cbn-[gState_recomp]. *)
  (*   - trans (reify (gReifiers_sReifier rs) (INPUT (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))). *)
  (*     { repeat f_equiv; eauto. *)
  (*       rewrite hom_INPUT. f_equiv. by intro. } *)
  (*     rewrite reify_vis_eq //; last first. *)
  (*     { rewrite subReifier_reify/=//. *)
  (*       rewrite H4. done. } *)
  (*     repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv. *)
  (*     rewrite interp_ectx_fill. *)
  (*     by rewrite ofe_iso_21. *)
  (*   - trans (reify (gReifiers_sReifier rs) (interp_ectx K env (OUTPUT n0)) (gState_recomp σr (sR_state σ))). *)
  (*     { do 3 f_equiv; eauto. *)
  (*       rewrite get_ret_ret//. } *)
  (*     trans (reify (gReifiers_sReifier rs) (OUTPUT_ n0 (interp_ectx K env (Ret 0))) (gState_recomp σr (sR_state σ))). *)
  (*     { do 2 f_equiv; eauto. *)
  (*       rewrite hom_OUTPUT_//. } *)
  (*     rewrite reify_vis_eq //; last first. *)
  (*     { rewrite subReifier_reify/=//. } *)
  (*     repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv. *)
  (*     rewrite interp_ectx_fill. *)
  (*     simpl. done. *)
  (* Qed. *)

  Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m env κ :
    prim_step e1 σ1 e2 σ2 (n,m) →
    ssteps (gReifiers_sReifier rs)
              (interp_expr e1 env κ) (gState_recomp σr (sR_state σ1))
              (interp_expr e2 env κ) (gState_recomp σr (sR_state σ2)) n.
  Proof.
    Opaque gState_decomp gState_recomp.
    inversion 1; simplify_eq/=.
    {
      destruct (head_step_io_01 _ _ _ _ _ _ _ H2); subst.
      - assert (σ1 = σ2) as ->.
        { eapply head_step_no_io; eauto. }
        admit.
        (* eapply (interp_expr_fill_no_reify K) in H2. *)
        (* rewrite H2. eapply ssteps_tick_n. *)
      - inversion H2;subst.
        + (* eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2. *)
          (* rewrite interp_ectx_fill. *)
          (* rewrite hom_INPUT. *)
          (* change 1 with (1+0). econstructor; last first. *)
          (* { apply ssteps_zero; reflexivity. } *)
          (* eapply sstep_reify. *)
          (* { Transparent INPUT. unfold INPUT. simpl. *)
          (*   f_equiv. reflexivity. } *)
          (* simpl in H2. *)
          (* rewrite -H2. *)
          (* repeat f_equiv; eauto. *)
          (* rewrite interp_ectx_fill hom_INPUT. *)
          (* eauto. *)
          admit.
        + (* eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2. *)
          (* rewrite interp_ectx_fill. simpl. *)
          (* rewrite get_ret_ret. *)
          (* rewrite hom_OUTPUT_. *)
          (* change 1 with (1+0). econstructor; last first. *)
          (* { apply ssteps_zero; reflexivity. } *)
          (* eapply sstep_reify. *)
          (* { Transparent OUTPUT_. unfold OUTPUT_. simpl. *)
          (*   f_equiv. reflexivity. } *)
          (* simpl in H2. *)
          (* rewrite -H2. *)
          (* repeat f_equiv; eauto. *)
          (* Opaque OUTPUT_. *)
          (* rewrite interp_ectx_fill /= get_ret_ret hom_OUTPUT_. *)
          (* eauto. *)
          admit.
    }
    {

    }
  Qed.

End interp.
#[global] Opaque INPUT OUTPUT_.
