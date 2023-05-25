From iris.proofmode Require Import classes tactics.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core.

Section reify.
  Definition reify_eff (E : opsInterp) (stateF : oFunctor) :=
    ∀ (op : opid E) (X : ofe) `{Cofe X},
    ((Ins (E op) ♯ X) * (stateF ♯ X) -n> optionO ((Outs (E op) ♯ X) * (stateF ♯ X)))%type.

  Inductive reifiers : opsInterp → Type :=
  | reifiers_nil : reifiers @[]
  | reifiers_cons
      (E : opsInterp) (stateF : oFunctor) (re : reify_eff E stateF)
      {Hinh : Inhabited (stateF ♯ unitO)}
      {Hcofe : forall X (HX : Cofe X), Cofe (stateF ♯ X)}
      {E'} (tail : reifiers E') : reifiers (opsInterp.app E E').

  Fixpoint reifiers_state {E} (rs : reifiers E) : oFunctor :=
    match rs with
    | reifiers_nil => unitO
    | reifiers_cons _ stateF _ tail => stateF * (reifiers_state tail)
    end.

  #[export] Instance reifiers_state_cofe E (rs : reifiers E) X `{!Cofe X} :
    Cofe (reifiers_state rs ♯ X).
  Proof. induction rs; simpl; apply _. Qed.
  #[export] Instance reifiers_state_inhab E (rs : reifiers E) :
    Inhabited (reifiers_state rs ♯ unitO).
  Proof. induction rs; simpl; apply _. Qed.


  Definition reifiers_re {E} (rs : reifiers E) (op : opid E) (X : ofe) `{Cofe X} :
    ((Ins (E op) ♯ X) * (reifiers_state rs ♯ X) → optionO ((Outs (E op) ♯ X) * (reifiers_state rs ♯ X)))%type.
  Proof.
    revert op. induction rs=>op.
    { apply Empty_set_rect. exact op. }
    simpl reifiers_state.
    destruct op as [op|op]; simpl.
    - refine (λ '(i,(s,s_rest)),
               '(o,s') ← re op X _ (i, s);
               Some (o,(s',s_rest))).
    - refine (λ '(i,(s,s_rest)),
               '(o,s'_rest) ← IHrs op (i,s_rest);
               Some (o,(s,s'_rest))
             ).
  Defined.

  #[global] Instance reifiers_re_ne {E} (rs : reifiers E) (op : opid E) (X : ofe) `{Cofe X} :
    NonExpansive (reifiers_re rs op X).
  Proof.
    induction rs; simpl.
    { apply Empty_set_rect. exact op. }
    destruct op as [op|op]; simpl.
    - intros n [x1 [s1 s1_rst]]  [x2 [s2 s2_rst]] [Hx [Hs Hsrest]].
      apply option_mbind_ne; last solve_proper.
      intros [o1 s'1] [o2 s'2] [Ho Hs']. solve_proper.
    - intros n [x1 [s1 s1_rst]]  [x2 [s2 s2_rst]] [Hx [Hs Hsrest]].
      apply option_mbind_ne; last solve_proper.
      intros [o1 s'1] [o2 s'2] [Ho Hs']. solve_proper.
  Qed.
  #[global] Instance reifiers_re_proper {E} (rs : reifiers E) (op : opid E) (X : ofe) `{Cofe X} :
    Proper ((≡) ==> (≡)) (reifiers_re rs op X).
  Proof. apply ne_proper. apply _. Qed.

  Variable (E : opsInterp) (rs : reifiers E).
  Notation IT := (IT E).
  Notation ITV := (ITV E).
  Notation stateF := (reifiers_state rs).

  Notation stateM := ((stateF ♯ IT -n> (stateF ♯ IT) * IT))%type.
  #[local] Instance stateT_inhab : Inhabited stateM.
  Proof.
    simple refine (populate (λne s, (s, Err))).
    solve_proper.
  Qed.
  #[local] Instance stateM_cofe : Cofe stateM.
  Proof. unfold stateM. apply _. Qed.

  Opaque laterO_map.

  Program Definition reify_fun : laterO (sumO IT stateM -n> prodO IT stateM) -n> stateM :=
    λne f s, (s, Fun $ laterO_map (λne f, fstO ◎ f ◎ inlO) f).
  Solve All Obligations with solve_proper.

  Program Definition reify_tau : laterO (prodO IT stateM) -n> stateM :=
    λne x s, (s, Tau $ laterO_map fstO x).
  Solve All Obligations with solve_proper.

  Program Definition reify_vis ( op : opid E ) :
   oFunctor_car (Ins (E op)) (sumO IT stateM) (prodO IT stateM) -n>
     (oFunctor_car (Outs (E op)) (prodO IT stateM) (sumO IT stateM) -n> laterO (prodO IT stateM)) -n> stateM.
  Proof.
    simpl.
    simple refine (λne i (k : _ -n> _) (s : stateF ♯ IT), _).
    - simple refine (let ns := reifiers_re rs op _ (oFunctor_map _ (inlO,fstO) i, s) in _).
      simple refine (from_option (λ ns,
                         let out2' := k $ oFunctor_map (Outs (E op)) (fstO,inlO) ns.1 in
                         (ns.2, Tau $ laterO_map fstO out2'))
                       (s, Err) ns).
    - intros n s1 s2 Hs. simpl. eapply (from_option_ne (dist n)); solve_proper.
    - intros n k1 k2 Hk s. simpl. eapply (from_option_ne (dist n)); solve_proper.
    - intros n i1 i2 Hi k s. simpl. eapply (from_option_ne (dist n)); solve_proper.
  Defined.

  Program Definition reify_err : stateM := λne s, (s, Err).
  Solve All Obligations with solve_proper.

  Program Definition reify_nat : natO -n> stateM := λne n s, (s, Nat n).
  Solve All Obligations with solve_proper.

  Program Definition unr : stateM -n>
    sumO (sumO (sumO (sumO natO unitO) (laterO (stateM -n> stateM))) (laterO stateM))
      (sigTO (λ op : opid E, prodO (oFunctor_apply (Ins (E op)) stateM) (oFunctor_apply (Outs (E op)) stateM -n> laterO stateM))).
  Proof. simple refine (λne d, inl (inl (inl (inr ())))). Qed.

  Definition reify : IT -n> stateM
    := IT_rec1 _
               reify_err
               reify_nat
               reify_fun
               reify_tau
               reify_vis
               unr.
  Definition unreify : stateM -n> IT
    := IT_rec2 _
               reify_err
               reify_nat
               reify_fun
               reify_tau
               reify_vis
               unr.

  Lemma reify_fun_eq f σ :
    reify (Fun f) σ ≡ (σ, Fun f).
  Proof.
    rewrite /reify/=.
    trans (reify_fun (laterO_map (sandwich (Perr:=reify_err) (Pnat:=reify_nat)
                                           (Parr:=reify_fun) (Ptau:=reify_tau)
                                           (Pvis:=reify_vis) (Punfold:=unr)
                                           stateM) f) σ).
    { f_equiv. apply IT_rec1_fun. }
    simpl. repeat f_equiv.
    rewrite -laterO_map_compose.
    trans (laterO_map idfun f).
    { repeat f_equiv. intros g x. done. }
    apply laterO_map_id.
  Qed.

  Lemma reify_vis_eq op i o k σ σ' :
    reifiers_re rs op _ (i,σ) ≡ Some (o,σ') →
    reify (Vis op i k) σ ≡ (σ', Tau $ k o).
  Proof.
    intros Hst.
    trans (reify_vis op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv.
      apply IT_rec1_vis. }
    Opaque prod_in. simpl.
    pose (r := (reifiers_re rs op _
      (oFunctor_map (Ins (E op)) (inlO, fstO)
                    (oFunctor_map (Ins (E op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold r.
    assert (r ≡ reifiers_re rs op _ (i,σ)) as Hr'.
    { unfold r. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (r ≡ Some (o,σ')) as Hr.
    { by rewrite Hr' Hst. }
    trans (from_option (λ ns,
       (ns.2,
        Tau
          (laterO_map fstO
             (laterO_map (prod_in idfun reify)
                (k
                   (oFunctor_map (Outs (E op)) (prod_in idfun reify, sumO_rec idfun unreify)
                      (oFunctor_map (Outs (E op)) (fstO, inlO) ns.1)))))))
             (σ, Err) (Some (o,σ'))).
    { apply from_option_proper; solve_proper. }
    simpl. repeat f_equiv.
    rewrite -laterO_map_compose.
    rewrite -oFunctor_map_compose.
    etrans; last by apply laterO_map_id.
    repeat f_equiv.
    { intro; done. }
    etrans; last by apply oFunctor_map_id.
    repeat f_equiv; intro; done.
  Qed.

  Lemma reify_vis_None op i k σ :
    reifiers_re rs op _ (i,σ) ≡ None →
    reify (Vis op i k) σ ≡ (σ, Err).
  Proof.
    intros Hs.
    trans (reify_vis op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv.
      apply IT_rec1_vis. }
    simpl.
    pose (r := (reifiers_re rs op _
      (oFunctor_map (Ins (E op)) (inlO, fstO)
                    (oFunctor_map (Ins (E op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold r.
    assert (r ≡ reifiers_re rs op _ (i,σ)) as Hr'.
    { unfold r. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (r ≡ None) as Hr.
    { by rewrite Hr' Hs. }
    trans (from_option (λ ns,
       (ns.2,
        Tau
          (laterO_map fstO
             (laterO_map (prod_in idfun reify)
                (k
                   (oFunctor_map (Outs (E op)) (prod_in idfun reify, sumO_rec idfun unreify)
                      (oFunctor_map (Outs (E op)) (fstO, inlO) ns.1)))))))
             (σ, Err) None).
    { apply from_option_proper; solve_proper. }
    reflexivity.
  Qed.

  Lemma reify_vis_cont op i k1 k2 σ1 σ2 β
    {PROP : bi} `{!BiInternalEq PROP} :
    (reify (Vis op i k1) σ1 ≡ (σ2, Tick β) ⊢
     reify (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡ (σ2, Tick (k2 β)) : PROP)%I.
  Proof.
    destruct (reifiers_re rs op _ (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
    - rewrite reify_vis_None; last by rewrite Hre//.
      iIntros "Hr". iExFalso.
      iPoseProof (prod_equivI with "Hr") as "[_ Hk]".
      simpl. iApply (IT_tick_err_ne). by iApply internal_eq_sym.
    - rewrite reify_vis_eq; last first.
      { by rewrite Hre. }
      rewrite reify_vis_eq; last first.
      { by rewrite Hre. }
      iIntros "Hr".
      iPoseProof (prod_equivI with "Hr") as "[Hs Hk]".
      iApply prod_equivI. simpl. iSplit; eauto.
      iPoseProof (Tau_inj' with "Hk") as "Hk".
      iApply Tau_inj'. iRewrite "Hk".
      rewrite laterO_map_Next. done.
  Qed.

  Lemma reify_input_cont_inv op i (k1 : _ -n> laterO IT) (k2 : IT -n> IT) σ1 σ2 β
    {PROP : bi} `{!BiInternalEq PROP} :
    (reify (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡ (σ2, Tick β)
     ⊢ ∃ α, reify (Vis op i k1) σ1 ≡ (σ2, Tick α) ∧ ▷ (β ≡ k2 α)
      : PROP)%I.
  Proof.
    destruct (reifiers_re rs op _ (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
    - rewrite reify_vis_None; last by rewrite Hre//.
      iIntros "Hr". iExFalso.
      iPoseProof (prod_equivI with "Hr") as "[_ Hk]".
      simpl. iApply (IT_tick_err_ne). by iApply internal_eq_sym.
    - rewrite reify_vis_eq; last first.
      { by rewrite Hre. }
      iIntros "Hr". simpl.
      iPoseProof (prod_equivI with "Hr") as "[#Hs #Hk]".
      simpl.
      iPoseProof (Tau_inj' with "Hk") as "Hk'".
      destruct (Next_uninj (k1 o)) as [a Hk1].
      iExists (a).
      rewrite reify_vis_eq; last first.
      { by rewrite Hre. }
      iSplit.
      + iApply prod_equivI. simpl. iSplit; eauto.
        iApply Tau_inj'. done.
      + iAssert (laterO_map k2 (Next a) ≡ Next β)%I as "Ha".
        { iSimpl in "Hk'". iRewrite -"Hk'".
          iPureIntro. rewrite -Hk1. done. }
        iAssert (Next (k2 a) ≡ Next β)%I as "Hb".
        { iRewrite -"Ha". iPureIntro.
          rewrite laterO_map_Next. done. }
        iNext. by iApply internal_eq_sym.
  Qed.

  Lemma reify_is_always_a_tick i op k σ β σ' :
    reify (Vis i op k) σ ≡ (σ', β) → (∃ β', β ≡ Tick β') ∨ (β ≡ Err).
  Proof.
    destruct (reifiers_re rs i _ (op, σ)) as [[o σ'']|] eqn:Hre; last first.
    - rewrite reify_vis_None; last by rewrite Hre//.
      intros [_ ?]. by right.
    - rewrite reify_vis_eq;last by rewrite Hre.
      intros [? Ho].
      destruct (Next_uninj (k o)) as [lβ Hlb].
      left. exists (lβ).
      rewrite Tick_eq.
      rewrite -Hlb. symmetry. apply Ho.
  Qed.

End reify.
Arguments reify {E} rs.

Class subState {E : opsInterp}
  (stateF : oFunctor) (rs : reifiers E) (rest : oFunctor) :=
  SubState
    { subS_decomp X `{Cofe X} :
         ofe_iso (reifiers_state rs ♯ X) ((stateF * rest) ♯ X);
    }.
Program Definition subState_conv_state {E} {stateF : oFunctor} {rs : reifiers E} `{!subState stateF rs rest} {X} `{!Cofe X} :
  (rest ♯ X) -n> (stateF ♯ X) -n> reifiers_state rs ♯ X :=
  λne rst s, ofe_iso_2 (subS_decomp _) (s,rst).
Solve Obligations with solve_proper.

#[export] Instance subState_here {F E} (stateF : oFunctor) (re : reify_eff F stateF)
  `{!Inhabited (stateF ♯ unitO)} `{forall X (HX : Cofe X), Cofe (stateF ♯ X)}
  (rs : reifiers E) : subState stateF (reifiers_cons F stateF re rs) (reifiers_state rs).
Proof.
  split. simpl. intros X HX. apply iso_ofe_refl.
Defined.

#[export] Instance subState_there {F E E'} {stateF stateE} (reE : reify_eff E stateE)
  (reF : reify_eff F stateF)
  `{!Inhabited (stateF ♯ unitO)} `{forall X (HX : Cofe X), Cofe (stateF ♯ X)}
  `{!Inhabited (stateE ♯ unitO)} `{forall X (HX : Cofe X), Cofe (stateE ♯ X)}
  (rs : reifiers E')
  `{!subState stateF rs rest}
  : subState stateF (reifiers_cons E stateE reE rs) (stateE * rest).
Proof.
  split. cbn-[oFunctor_apply].
  intros X HX.
  unshelve esplit.
  - simple refine (λne sx, let y := ofe_iso_1 (subS_decomp _) sx.2 in
                           (y.1, (sx.1,y.2))).
    + apply _.
    + solve_proper.
  - simple refine (λne fer, let y := ofe_iso_2 (subS_decomp _) (fer.1,fer.2.2) in
                            (fer.2.1,y)).
    + apply _.
    + solve_proper.
  - intros (f & e & r). simpl. rewrite ofe_iso_12. done.
  - intros (e & r). simpl. f_equiv.
    rewrite -surjective_pairing.
    rewrite ofe_iso_21. done.
Defined.

Class subReifier {F E : opsInterp} {stateF}
  (re : reify_eff F stateF) (rs : reifiers E) (rest : oFunctor) :=
  SubReifier
    { subR_subEff :: subEff F E;
      subR_subS   :: subState stateF rs rest;
      subR_reify (op : opid F) X `{Cofe X}
        (i : Ins (F op) ♯ X) (s : stateF ♯ X) (s_rest : rest ♯ X) :
        let i' := subEff_conv_ins i in
        let s' := subState_conv_state s_rest s in
        reifiers_re rs (subEff_opid op) X (i',s') ≡
          optionO_map (prodO_map subEff_conv_outs (subState_conv_state s_rest))
                      (re op X _ (i,s))
    }.

#[export] Instance subReifier_here {F E} {stateF} (re : reify_eff F stateF)
  `{!Inhabited (stateF ♯ unitO)} `{forall X (HX : Cofe X), Cofe (stateF ♯ X)}
  (rs : reifiers E) : subReifier re (reifiers_cons F stateF re rs) (reifiers_state rs).
Proof.
  esplit; try apply _.
  intros op X HX i s rest. simpl.
  destruct (re op X HX (i, s)) as [[o s']|] eqn:Hre;
    rewrite Hre; reflexivity.
Defined. (* we need it to be able to simplify .. *)

#[export] Instance subReifier_there {F E E'} {stateF stateE}
  (reE : reify_eff E stateE)
  (reF : reify_eff F stateF)
  `{!Inhabited (stateF ♯ unitO)} `{forall X (HX : Cofe X), Cofe (stateF ♯ X)}
  `{!Inhabited (stateE ♯ unitO)} `{forall X (HX : Cofe X), Cofe (stateE ♯ X)}
  (rs : reifiers E')
  `{!subReifier reF rs rest}
  : subReifier reF (reifiers_cons E stateE reE rs) (stateE * rest).
Proof.
  unshelve esplit.
  { eapply subState_there; eauto. apply _. } (** XXX: why does typeclass search fail? *)
  intros op X HX i s s_rest.
  destruct (subState_conv_state s_rest s) as [sE' sR] eqn:Hdecomp.
  destruct s_rest as [sE s_rest].
  simpl in Hdecomp.
  simplify_eq/=.
  change (ofe_iso_2 (subS_decomp X) (s, s_rest)) with (subState_conv_state s_rest s).
  assert
    (reifiers_re rs (subEff_opid op) X (subEff_conv_ins i, subState_conv_state s_rest s) ≡ optionO_map (prodO_map subEff_conv_outs (subState_conv_state s_rest))
       (reF op X HX (i, s))) as HH.
  { apply subR_reify. }
  revert HH.
  destruct (reF op X HX (i, s)) as [[o s']|] eqn:HreF; simpl.
  - destruct (reifiers_re rs (subEff_opid op) X
                (subEff_conv_ins i, subState_conv_state s_rest s))
      as [[o' s'_rest]|] eqn:Hre.
    + rewrite Hre. simpl. intros [Ho Hs]%Some_equiv_inj%pair_equiv_inj.
      solve_proper.
    + rewrite Hre. simpl. inversion 1.
  - destruct (reifiers_re rs (subEff_opid op) X
                (subEff_conv_ins i, subState_conv_state s_rest s))
      as [[o' s'_rest]|] eqn:Hre.
    + rewrite Hre. simpl. inversion 1.
    + rewrite Hre. simpl. done.
Defined. (* ditto *)

