(** Call/cc + throw effects *)
From gitrees Require Import prelude gitree.

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

  Lemma wp_throw'' σ κ (f : IT -> IT) (x : IT)
    (HE : NonExpansive f)
    `{!IT_hom κ} Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} f x @ s {{ Φ }}) -∗
    WP@{rs} κ (THROW x (Next (λne x, f x))) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha". rewrite /THROW. simpl.
    rewrite hom_vis.
    iApply (wp_subreify_ctx_dep with "Hs"); simpl; done.
  Qed.

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
End weakestpre.
