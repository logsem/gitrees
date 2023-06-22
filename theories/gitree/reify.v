From iris.proofmode Require Import classes tactics.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core.

Section reifiers.
  #[local] Open Scope type.

  (** A single reifier *)
  Record sReifier :=
    { sReifier_ops : opsInterp;
      sReifier_state : oFunctor;
      sReifier_re {X} `{!Cofe X} : forall (op : opid sReifier_ops),
          (Ins (sReifier_ops op) ♯ X) * (sReifier_state ♯ X)
              -n> optionO ((Outs (sReifier_ops op) ♯ X) * (sReifier_state ♯ X));
      sReifier_inhab :: Inhabited (sReifier_state ♯ unitO);
      sReifier_cofe X (HX : Cofe X) :: Cofe (sReifier_state ♯ X);
    }.

  Context (r : sReifier).
  Notation F := (sReifier_ops r).
  Notation stateF := (sReifier_state r).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Notation stateM := ((stateF ♯ IT -n> (stateF ♯ IT) * IT)).
  #[local] Instance stateT_inhab : Inhabited stateM.
  Proof.
    simple refine (populate (λne s, (s, inhabitant))).
    { apply _. }
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

  Program Definition reify_vis ( op : opid F ) :
   oFunctor_car (Ins (F op)) (sumO IT stateM) (prodO IT stateM) -n>
     (oFunctor_car (Outs (F op)) (prodO IT stateM) (sumO IT stateM) -n> laterO (prodO IT stateM)) -n> stateM.
  Proof.
    simpl.
    simple refine (λne i (k : _ -n> _) (s : stateF ♯ IT), _).
    - simple refine (let ns := sReifier_re r op (oFunctor_map _ (inlO,fstO) i, s) in _).
      simple refine (from_option (λ ns,
                         let out2' := k $ oFunctor_map (Outs (F op)) (fstO,inlO) ns.1 in
                         (ns.2, Tau $ laterO_map fstO out2'))
                       (s, Err RuntimeErr) ns).
    - intros m s1 s2 Hs. simpl. eapply (from_option_ne (dist m)); solve_proper.
    - intros m k1 k2 Hk s. simpl. eapply (from_option_ne (dist m)); solve_proper.
    - intros m i1 i2 Hi k s. simpl. eapply (from_option_ne (dist m)); solve_proper.
  Defined.

  Program Definition reify_err : errorO -n> stateM := λne e s, (s, Err e).
  Solve All Obligations with solve_proper.

  Program Definition reify_nat : natO -n> stateM := λne n s, (s, Nat n).
  Solve All Obligations with solve_proper.

  Program Definition unr : stateM -n>
    sumO (sumO (sumO (sumO natO (laterO (stateM -n> stateM))) errorO) (laterO stateM))
      (sigTO (λ op : opid F, prodO (oFunctor_apply (Ins (F op)) stateM) (oFunctor_apply (Outs (F op)) stateM -n> laterO stateM))).
  Proof. simple refine (λne d, inl (inl (inr (RuntimeErr)))). Qed.

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

  Lemma reify_vis_dist m op i o k σ σ' :
    sReifier_re r op (i,σ) ≡{m}≡ Some (o,σ') →
    reify (Vis op i k) σ ≡{m}≡ (σ', Tau $ k o).
  Proof.
    intros Hst.
    trans (reify_vis op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv. rewrite IT_rec1_vis//. }
    Opaque prod_in. simpl.
    pose (rs := (sReifier_re r op
      (oFunctor_map (Ins (F op)) (inlO, fstO)
                    (oFunctor_map (Ins (F op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold rs.
    assert (rs ≡ sReifier_re r op (i,σ)) as Hr'.
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
                   (oFunctor_map (Outs (F op)) (prod_in idfun reify, sumO_rec idfun unreify)
                      (oFunctor_map (Outs (F op)) (fstO, inlO) ns.1)))))))
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

  Lemma reify_vis_eq op i o k σ σ' :
    sReifier_re r op (i,σ) ≡ Some (o,σ') →
    reify (Vis op i k) σ ≡ (σ', Tau $ k o).
  Proof.
    intros H. apply equiv_dist=>m.
    apply reify_vis_dist.
    by apply equiv_dist.
  Qed.

  Lemma reify_vis_None op i k σ :
    sReifier_re r op (i,σ) ≡ None →
    reify (Vis op i k) σ ≡ (σ, Err RuntimeErr).
  Proof.
    intros Hs.
    trans (reify_vis op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv.
      apply IT_rec1_vis. }
    simpl.
    pose (rs := (sReifier_re r op
      (oFunctor_map (Ins (F op)) (inlO, fstO)
                    (oFunctor_map (Ins (F op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold rs.
    assert (rs ≡ sReifier_re r op (i,σ)) as Hr'.
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
                   (oFunctor_map (Outs (F op)) (prod_in idfun reify, sumO_rec idfun unreify)
                      (oFunctor_map (Outs (F op)) (fstO, inlO) ns.1)))))))
             (σ, Err RuntimeErr) None).
    { apply from_option_proper; solve_proper. }
    reflexivity.
  Qed.

  Lemma reify_vis_cont op i k1 k2 σ1 σ2 β
    {PROP : bi} `{!BiInternalEq PROP} :
    (reify (Vis op i k1) σ1 ≡ (σ2, Tick β) ⊢
     reify (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡ (σ2, Tick (k2 β)) : PROP)%I.
  Proof.
    destruct (sReifier_re r op (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
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
    destruct (sReifier_re r op (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
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

  Lemma reify_is_always_a_tick op x k σ β σ' :
    reify (Vis op x k) σ ≡ (σ', β) → (∃ β', β ≡ Tick β') ∨ (β ≡ Err RuntimeErr).
  Proof.
    destruct (sReifier_re r op (x, σ)) as [[o σ'']|] eqn:Hre; last first.
    - rewrite reify_vis_None; last by rewrite Hre//.
      intros [_ ?]. by right.
    - rewrite reify_vis_eq;last by rewrite Hre.
      intros [? Ho].
      destruct (Next_uninj (k o)) as [lβ Hlb].
      left. exists (lβ).
      rewrite Tick_eq.
      rewrite -Hlb. symmetry. apply Ho.
  Qed.

End reifiers.

