From iris.proofmode Require Import classes tactics.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core.

Section reifier.
  Inductive is_ctx_dep : Type :=
  | CtxDep
  | NotCtxDep.

  Context {A} `{!Cofe A} (icd : is_ctx_dep).
  #[local] Open Scope type.

  (** A single reifier *)
  Record sReifier :=
    { sReifier_ops : opsInterp;
      sReifier_state : oFunctor;
      sReifier_re {X} `{!Cofe X} : forall (op : opid sReifier_ops),
        match icd with
        | CtxDep =>
            (Ins (sReifier_ops op) ♯ X)
            * (sReifier_state ♯ X)
            * ((Outs (sReifier_ops op) ♯ X) -n> laterO X)
            -n> optionO (laterO X * (sReifier_state ♯ X))
        | NotCtxDep =>
            (Ins (sReifier_ops op) ♯ X)
            * (sReifier_state ♯ X)
            -n> optionO ((Outs (sReifier_ops op) ♯ X) * (sReifier_state ♯ X))
        end;
      sReifier_inhab :: Inhabited (sReifier_state ♯ unitO);
      sReifier_cofe X (HX : Cofe X) :: Cofe (sReifier_state ♯ X);
    }.
End reifier.

Section reifier_cofe_inst.
  Context {A} `{!Cofe A}.
  #[local] Open Scope type.
  Notation F a r := (sReifier_ops a r).
  Notation stateF a r := (sReifier_state a r).
  Notation IT a r := (IT (F a r) A).
  Notation ITV a r := (ITV (F a r) A).
  Notation stateM a r := ((stateF a r) ♯ (IT a r) -n> ((stateF a r) ♯ (IT a r)) * (IT a r)).

  #[global] Instance stateT_inhab {a r} : Inhabited (stateM a r).
  Proof.
    simple refine (populate (λne s, (s, inhabitant))).
    { apply _. }
    solve_proper.
  Qed.
  #[global] Instance stateM_cofe {a r} : Cofe (stateM a r).
  Proof. unfold stateM. apply _. Qed.

End reifier_cofe_inst.

Section reifier_vis.
  Context {A} `{!Cofe A}.
  #[local] Open Scope type.
  Notation F a r := (sReifier_ops a r).
  Notation stateF a r := (sReifier_state a r).
  Notation IT a r := (IT (F a r) A).
  Notation ITV a r := (ITV (F a r) A).
  Notation stateM a r := ((stateF a r) ♯ (IT a r) -n> ((stateF a r) ♯ (IT a r)) * (IT a r)).

  Program Definition reify_vis_ctx_dep (r : sReifier CtxDep) ( op : opid (F CtxDep r)) :
    oFunctor_car (Ins (F CtxDep r op))
      (sumO (IT CtxDep r) (stateM CtxDep r)) (prodO (IT CtxDep r) (stateM CtxDep r)) -n>
      (oFunctor_car (Outs (F CtxDep r op)) (prodO (IT CtxDep r) (stateM CtxDep r))
         (sumO (IT CtxDep r) (stateM CtxDep r))
       -n> laterO (prodO (IT CtxDep r) (stateM CtxDep r))) -n> (stateM CtxDep r).
  Proof.
    simpl.
    simple refine (λne i (k : _ -n> _) (s : stateF CtxDep r ♯ (IT CtxDep r)), _).
    - simple refine
        (let ns := sReifier_re CtxDep r op
                     (oFunctor_map _ (inlO,fstO) i, s,
                       (λne o, (laterO_map fstO $ k
                                  $ oFunctor_map (Outs (F CtxDep r op)) (fstO, inlO) o))) in _).
      + intros m s1 s2 Hs. solve_proper.
      + simple refine (from_option (λ ns,
                           (ns.2, Tau $ ns.1))
                         (s, Err RuntimeErr) ns).
    - intros m s1 s2 Hs. simpl. eapply (from_option_ne (dist m)); solve_proper.
    - intros m k1 k2 Hk s. simpl. eapply (from_option_ne (dist m)); [solve_proper | solve_proper |].
      do 2 f_equiv.
      solve_proper.
    - intros m i1 i2 Hi k s. simpl. eapply (from_option_ne (dist m)); solve_proper.
  Defined.

  Program Definition reify_vis_ctx_indep (r : sReifier NotCtxDep) ( op : opid (F NotCtxDep r) ) :
    oFunctor_car (Ins (F NotCtxDep r op)) (sumO (IT NotCtxDep r) (stateM NotCtxDep r))
      (prodO (IT NotCtxDep r) (stateM NotCtxDep r)) -n>
      (oFunctor_car (Outs (F NotCtxDep r op)) (prodO (IT NotCtxDep r) (stateM NotCtxDep r))
         (sumO (IT NotCtxDep r) (stateM NotCtxDep r))
       -n> laterO (prodO (IT NotCtxDep r) (stateM NotCtxDep r))) -n> (stateM NotCtxDep r).
  Proof.
    simpl.
    simple refine (λne i (k : _ -n> _) (s : stateF NotCtxDep r ♯ (IT NotCtxDep r)), _).
    - simple refine (let ns := sReifier_re NotCtxDep r op (oFunctor_map _ (inlO,fstO) i, s) in _).
      simple refine (from_option (λ ns,
                         let out2' := k $ oFunctor_map (Outs (F NotCtxDep r op)) (fstO,inlO) ns.1 in
                         (ns.2, Tau $ laterO_map fstO out2'))
                       (s, Err RuntimeErr) ns).
    - intros m s1 s2 Hs. simpl. eapply (from_option_ne (dist m)); solve_proper.
    - intros m k1 k2 Hk s. simpl. eapply (from_option_ne (dist m)); solve_proper.
    - intros m i1 i2 Hi k s. simpl. eapply (from_option_ne (dist m)); solve_proper.
  Defined.

  Program Definition reify_vis (a : is_ctx_dep) (r : sReifier a) : ∀ ( op : opid (F a r)),
    oFunctor_car (Ins (F a r op)) (sumO (IT a r) (stateM a r)) (prodO (IT a r) (stateM a r)) -n>
      (oFunctor_car (Outs (F a r op)) (prodO (IT a r) (stateM a r))
         (sumO (IT a r) (stateM a r)) -n> laterO (prodO (IT a r) (stateM a r))) -n> (stateM a r).
  Proof.
    destruct a.
    - apply reify_vis_ctx_dep.
    - apply reify_vis_ctx_indep.
  Defined.
End reifier_vis.

Section reify.
  Context {A} `{!Cofe A} {a : is_ctx_dep}.
  #[local] Open Scope type.
  Context {r : sReifier a}.
  Notation F := (sReifier_ops a r).
  Notation stateF := (sReifier_state a r).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateM := (stateF ♯ IT -n> (stateF ♯ IT) * IT).

  Opaque laterO_map.

  Program Definition reify_fun : laterO (sumO IT stateM -n> prodO IT stateM) -n> stateM :=
    λne f s, (s, Fun $ laterO_map (λne f, fstO ◎ f ◎ inlO) f).
  Solve All Obligations with solve_proper.

  Program Definition reify_tau : laterO (prodO IT stateM) -n> stateM :=
    λne x s, (s, Tau $ laterO_map fstO x).
  Solve All Obligations with solve_proper.

  Program Definition reify_err : errorO -n> stateM := λne e s, (s, Err e).
  Solve All Obligations with solve_proper.

  Program Definition reify_ret : A -n> stateM := λne n s, (s, Ret n).
  Solve All Obligations with solve_proper.

  Program Definition unr : stateM -n>
                             sumO (sumO (sumO (sumO A (laterO (stateM -n> stateM))) errorO) (laterO stateM))
                               (sigTO (λ op : opid F, prodO (oFunctor_apply (Ins (F op)) stateM)
                                                        (oFunctor_apply (Outs (F op)) stateM -n> laterO stateM))).
  Proof. simple refine (λne d, inl (inl (inr (RuntimeErr)))). Qed.

  Definition reify : IT -n> stateM
    := IT_rec1 _
         reify_err
         reify_ret
         reify_fun
         reify_tau
         (reify_vis a r)
         unr.
  Definition unreify : stateM -n> IT
    := IT_rec2 _
         reify_err
         reify_ret
         reify_fun
         reify_tau
         (reify_vis a r)
         unr.

  Lemma reify_fun_eq f σ :
    reify (Fun f) σ ≡ (σ, Fun f).
  Proof.
    rewrite /reify/=.
    trans (reify_fun (laterO_map (sandwich (Perr:=reify_err) (Pret:=reify_ret)
                                    (Parr:=reify_fun) (Ptau:=reify_tau)
                                    (Pvis:=reify_vis a r) (Punfold:=unr)
                                    (stateM)) f) σ).
    { f_equiv. apply IT_rec1_fun. }
    simpl. repeat f_equiv.
    rewrite -laterO_map_compose.
    trans (laterO_map idfun f).
    { repeat f_equiv. intros g x. done. }
    apply laterO_map_id.
  Qed.

End reify.

Section reify_props.
  Context {A} `{!Cofe A}.
  #[local] Open Scope type.
  Notation F a r := (sReifier_ops a r).
  Notation stateF a r := (sReifier_state a r).
  Notation IT a r := (IT (F a r) A).
  Notation ITV a r := (ITV (F a r) A).
  Notation stateM a r := (stateF a r ♯ (IT a r) -n> (stateF a r ♯ (IT a r)) * (IT a r)).

  Opaque laterO_map.

  Lemma reify_vis_dist_ctx_dep (r : sReifier CtxDep) m op i o k σ σ' :
    @sReifier_re CtxDep r (IT CtxDep r) _ op (i, σ, k) ≡{m}≡ Some (o, σ') →
    reify (Vis op i k) σ ≡{m}≡ (σ', Tau o).
  Proof.
    intros Hst.
    trans (reify_vis CtxDep r op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k
                ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv. rewrite IT_rec1_vis//. }
    Opaque prod_in. simpl.
    pose (rs := (sReifier_re _ r op
                   (oFunctor_map (Ins (F _ _ op)) (inlO, fstO)
                      (oFunctor_map (Ins (F _ _ op))
                         (sumO_rec idfun unreify, prod_in idfun reify) i), σ, k))).
    fold rs.
    assert (rs ≡ sReifier_re _ r op (i,σ, k)) as Hr'.
    { unfold rs. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      f_equiv.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (rs ≡{m}≡ Some (o, σ')) as Hr.
    { by rewrite Hr' Hst. }
    trans (from_option (λ ns : laterO (IT _ _) * (stateF _ _) ♯ (IT _ _), (ns.2, Tau ns.1))
             (σ, Err RuntimeErr)
             rs).
    - subst rs.
      eapply (from_option_ne (dist m)); [solve_proper | solve_proper |].
      do 2 f_equiv.
      intros ?; simpl.
      rewrite -laterO_map_compose.
      rewrite -oFunctor_map_compose.
      etrans; first (rewrite laterO_map_id; reflexivity).
      f_equiv.
      trans (oFunctor_map _ (idfun, idfun) x).
      + do 3 f_equiv.
        * intros y; simpl.
          Transparent prod_in.
          by unfold prod_in.
        * intros y; simpl.
          reflexivity.
      + by rewrite oFunctor_map_id.
    - subst rs.
      trans (from_option (λ ns : laterO (IT _ _) * (stateF _ _) ♯ (IT _ _), (ns.2, Tau ns.1))
               (σ, Err RuntimeErr)
               (Some (o, σ'))).
      + eapply (from_option_ne (dist m)); [solve_proper | solve_proper |].
        by rewrite Hr.
      + reflexivity.
  Qed.

  Lemma reify_vis_dist_ctx_indep (r : sReifier NotCtxDep) m op i o k σ σ' :
    @sReifier_re NotCtxDep r (IT NotCtxDep r) _ op (i,σ) ≡{m}≡ Some (o,σ') →
    reify (Vis op i k) σ ≡{m}≡ (σ', Tau $ k o).
  Proof.
    intros Hst.
    trans (reify_vis _ _ op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k
                ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv. rewrite IT_rec1_vis//. }
    Opaque prod_in. simpl.
    pose (rs := (@sReifier_re NotCtxDep r _ _ op
                   (oFunctor_map (Ins (F NotCtxDep r op)) (inlO, fstO)
                      (oFunctor_map (Ins (F NotCtxDep r op))
                         (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold rs.
    assert (rs ≡ sReifier_re NotCtxDep r op (i,σ)) as Hr'.
    { unfold rs. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (rs ≡{m}≡ Some (o,σ')) as Hr.
    { by rewrite Hr' Hst. }
    trans (from_option (λ ns,
               (ns.2,
                 Tau
                   (laterO_map fstO
                      (laterO_map (prod_in idfun reify)
                         (k
                            (oFunctor_map (Outs (F NotCtxDep r op))
                               (prod_in idfun reify, sumO_rec idfun unreify)
                               (oFunctor_map (Outs (F NotCtxDep r op)) (fstO, inlO) ns.1)))))))
             (σ, Err RuntimeErr) (Some (o,σ'))).
    { eapply (from_option_ne (dist m)); solve_proper. }
    simpl. repeat f_equiv.
    rewrite -laterO_map_compose.
    rewrite -oFunctor_map_compose.
    trans (laterO_map idfun (k o)); last first.
    { by rewrite laterO_map_id. }
    repeat f_equiv.
    { intro; done. }
    trans (oFunctor_map _ (idfun, idfun) o); last first.
    { by rewrite oFunctor_map_id.  }
    simpl.
    repeat f_equiv; intro; done.
  Qed.

  Lemma reify_vis_eq_ctx_dep r op i o k σ σ' :
    @sReifier_re CtxDep r (IT CtxDep r) _ op (i,σ,k) ≡ Some (o,σ') →
    reify (Vis op i k) σ ≡ (σ', Tau $ o).
  Proof.
    intros H. apply equiv_dist=>m.
    apply reify_vis_dist_ctx_dep.
    by apply equiv_dist.
  Qed.

  Lemma reify_vis_eq_ctx_indep r op i o k σ σ' :
    @sReifier_re NotCtxDep r (IT NotCtxDep r) _ op (i,σ) ≡ Some (o,σ') →
    reify (Vis op i k) σ ≡ (σ', Tau $ k o).
  Proof.
    intros H. apply equiv_dist=>m.
    apply reify_vis_dist_ctx_indep.
    by apply equiv_dist.
  Qed.

  Lemma reify_vis_None_ctx_dep r op i k σ :
    @sReifier_re CtxDep r (IT CtxDep r) _ op (i,σ,k) ≡ None →
    reify (Vis op i k) σ ≡ (σ, Err RuntimeErr).
  Proof.
    intros Hs.
    trans (reify_vis _ _ op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k
                ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv.
      apply IT_rec1_vis. }
    simpl.
    pose (rs := (sReifier_re CtxDep r op
                   (oFunctor_map (Ins (F CtxDep r op)) (inlO, fstO)
                      (oFunctor_map (Ins (F CtxDep r op))
                         (sumO_rec idfun unreify, prod_in idfun reify) i), σ, k))).
    fold rs.
    assert (rs ≡ sReifier_re CtxDep r op (i,σ, k)) as Hr'.
    { unfold rs. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      f_equiv.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (rs ≡ None) as Hr.
    { by rewrite Hr' Hs. }
    trans (from_option (λ ns : laterO (IT _ _) * (stateF _ _) ♯ (IT _ _), (ns.2, Tau ns.1))
             (σ, Err RuntimeErr)
             rs).
    {
      apply from_option_proper; [solve_proper | solve_proper |].
      subst rs.
      do 2 f_equiv.
      intros x; simpl.
      rewrite -laterO_map_compose -oFunctor_map_compose.
      trans (laterO_map idfun (k x)); last first.
      { by rewrite laterO_map_id. }
      f_equiv; first (f_equiv; intros ?; reflexivity).
      f_equiv.
      trans (oFunctor_map _ (idfun, idfun) x).
      - do 3 f_equiv.
        + intros y; simpl.
          Transparent prod_in.
          by unfold prod_in.
        + intros y; simpl.
          reflexivity.
      - by rewrite oFunctor_map_id.
    }
    trans (from_option (λ ns : laterO (IT CtxDep r) * (stateF _ _) ♯ (IT _ _),
                 (ns.2, Tau ns.1)) (σ, Err RuntimeErr) None).
    - f_equiv; [| assumption].
      intros [? ?] [? ?] [? ?]; simpl in *; f_equiv; [assumption | f_equiv; assumption].
    - reflexivity.
  Qed.

  Lemma reify_vis_None_ctx_indep r op i k σ :
    @sReifier_re NotCtxDep r (IT NotCtxDep r) _ op (i,σ) ≡ None →
    reify (Vis op i k) σ ≡ (σ, Err RuntimeErr).
  Proof.
    intros Hs.
    trans (reify_vis _ _ op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k
                ◎ (oFunctor_map _
                     (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv.
      apply IT_rec1_vis. }
    simpl.
    pose (rs := (sReifier_re NotCtxDep r op
                   (oFunctor_map (Ins (F _ _ op)) (inlO, fstO)
                      (oFunctor_map (Ins (F _ _ op))
                         (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold rs.
    assert (rs ≡ sReifier_re _ r op (i,σ)) as Hr'.
    { unfold rs. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (rs ≡ None) as Hr.
    { by rewrite Hr' Hs. }
    trans (from_option (λ ns,
               (ns.2,
                 Tau
                   (laterO_map fstO
                      (laterO_map (prod_in idfun reify)
                         (k
                            (oFunctor_map (Outs (F _ _ op))
                               (prod_in idfun reify, sumO_rec idfun unreify)
                               (oFunctor_map (Outs (F _ _ op)) (fstO, inlO) ns.1)))))))
             (σ, Err RuntimeErr) None).
    { apply from_option_proper; solve_proper. }
    reflexivity.
  Qed.

  Lemma reify_is_always_a_tick {a : is_ctx_dep} r op x k σ β σ' :
    reify (a := a) (A := A) (r := r) (Vis op x k) σ ≡ (σ', β)
    → (∃ β', β ≡ Tick β') ∨ (β ≡ Err RuntimeErr).
  Proof.
    destruct a.
    {
      destruct (sReifier_re _ r op (x, σ, k)) as [[o σ'']|] eqn:Hre; last first.
      - rewrite reify_vis_None_ctx_dep; last by rewrite Hre//.
        intros [_ ?]. by right.
      - rewrite reify_vis_eq_ctx_dep;last by rewrite Hre.
        intros [? Ho].
        left.
        simpl in *.
        destruct (Next_uninj o) as [t Ht].
        exists (t).
        rewrite <-Ho.
        rewrite Ht.
        reflexivity.
    }
    {
      destruct (sReifier_re _ r op (x, σ)) as [[o σ'']|] eqn:Hre; last first.
      - rewrite reify_vis_None_ctx_indep; last by rewrite Hre//.
        intros [_ ?]. by right.
      - rewrite reify_vis_eq_ctx_indep;last by rewrite Hre.
        intros [? Ho].
        destruct (Next_uninj (k o)) as [lβ Hlb].
        left. exists (lβ).
        rewrite Tick_eq.
        rewrite -Hlb. symmetry. apply Ho.
    }
  Qed.

  Lemma reify_vis_cont r op i k1 k2 σ1 σ2 β
    {PROP : bi} `{!BiInternalEq PROP} :
    (reify (a := NotCtxDep) (A := A) (r := r) (Vis op i k1) σ1 ≡ (σ2, Tick β) ⊢
     reify (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡ (σ2, Tick (k2 β)) : PROP)%I.
  Proof.
    destruct (sReifier_re _ r op (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
    - rewrite reify_vis_None_ctx_indep; last by rewrite Hre//.
      iIntros "Hr". iExFalso.
      iPoseProof (prod_equivI with "Hr") as "[_ Hk]".
      simpl. iApply (IT_tick_err_ne). by iApply internal_eq_sym.
    - rewrite reify_vis_eq_ctx_indep; last first.
      { by rewrite Hre. }
      rewrite reify_vis_eq_ctx_indep; last first.
      { by rewrite Hre. }
      iIntros "Hr".
      iPoseProof (prod_equivI with "Hr") as "[Hs Hk]".
      iApply prod_equivI. simpl. iSplit; eauto.
      iPoseProof (Tau_inj' with "Hk") as "Hk".
      iApply Tau_inj'. iRewrite "Hk".
      rewrite laterO_map_Next. done.
  Qed.

  Lemma reify_input_cont_inv r op i (k1 : _ -n> laterO (IT NotCtxDep r))
    (k2 : IT _ r -n> IT _ r) σ1 σ2 β
    {PROP : bi} `{!BiInternalEq PROP} :
    (reify (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡ (σ2, Tick β)
     ⊢ ∃ α, reify (Vis op i k1) σ1 ≡ (σ2, Tick α) ∧ ▷ (β ≡ k2 α)
         : PROP)%I.
  Proof.
    destruct (sReifier_re _ r op (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
    - rewrite reify_vis_None_ctx_indep; last by rewrite Hre//.
      iIntros "Hr". iExFalso.
      iPoseProof (prod_equivI with "Hr") as "[_ Hk]".
      simpl. iApply (IT_tick_err_ne). by iApply internal_eq_sym.
    - rewrite reify_vis_eq_ctx_indep; last first.
      { by rewrite Hre. }
      iIntros "Hr". simpl.
      iPoseProof (prod_equivI with "Hr") as "[#Hs #Hk]".
      simpl.
      iPoseProof (Tau_inj' with "Hk") as "Hk'".
      destruct (Next_uninj (k1 o)) as [a Hk1].
      iExists (a).
      rewrite reify_vis_eq_ctx_indep; last first.
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
End reify_props.

Arguments reify {_ _ _} _.
