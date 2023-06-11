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

  (** Global reifiers: a collection of reifiers *)
  Inductive gReifiers : nat → Type :=
  | gReifiers_nil : gReifiers 0
  | gReifiers_cons {n} : sReifier → gReifiers n → gReifiers (S n)
  .

  Definition grs_S_inv {n} (P : gReifiers (S n) → Type)
    (Hcons : ∀ sR v, P (gReifiers_cons sR v)) v : P v.
  Proof.
    revert P Hcons.
    refine match v with gReifiers_nil => tt
                      | gReifiers_cons sR v => λ P Hcons, Hcons sR v end.
  Defined.

  #[global] Instance gReifiers_lookup_total : ∀ m, LookupTotal (fin m) sReifier (gReifiers m) :=
  fix go m i {struct i} := let _ : ∀ m, LookupTotal _ _ _ := @go in
  match i in fin m return gReifiers m → sReifier with
  | 0%fin => grs_S_inv (λ _, sReifier) (λ x _, x)
  | FS j => grs_S_inv (λ _, sReifier) (λ _ v, v !!! j)
  end.

  Program Definition gReifiers_ops {n} (rs : gReifiers n) : opsInterp :=
    {| opid := { i : fin n & opid (sReifier_ops (rs !!! i)) };
       opsInterp_lookup := λ iop, sReifier_ops (rs !!! projT1 iop) (projT2 iop)
    |}.
  Next Obligation.
    intros n rs.
    unfold EqDecision. intros [i1 x1] [i2 x2].
    unfold Decision.
    destruct (decide (i1 = i2)) as [<-|Hi].
    - destruct (decide (x1 = x2)) as [<-|Hx].
      + left. reflexivity.
      + right. naive_solver.
    - right. naive_solver.
  Qed.

  Fixpoint gReifiers_state {n} (rs : gReifiers n) : oFunctor :=
    match rs with
    | gReifiers_nil => unitO
    | gReifiers_cons sR rs => sReifier_state sR * (gReifiers_state rs)
    end.

  #[export] Instance reifiers_state_cofe {n} (rs : gReifiers n) X `{!Cofe X} :
    Cofe (gReifiers_state rs ♯ X).
  Proof.
    induction rs; simpl; first apply _.
    destruct s. apply _.
  Qed.
  #[export] Instance reifiers_state_inhab {n} (rs : gReifiers n) :
    Inhabited (gReifiers_state rs ♯ unitO).
  Proof.
    induction rs; simpl; first apply _.
    destruct s. apply _.
  Qed.

  Fixpoint gState_rest {m} (i : fin m) : gReifiers m → oFunctor :=
    match i in fin m return gReifiers m → oFunctor with
    | 0%fin => grs_S_inv (λ _, oFunctor)
                 (λ sR rs, gReifiers_state rs)
    | FS j => grs_S_inv (λ _, oFunctor)
                 (λ sR rs, sReifier_state sR * gState_rest j rs)%OF
    end.

  Lemma gState_decomp' {m} (i : fin m) (rs : gReifiers m) {X} `{!Cofe X} :
    ofe_iso (gReifiers_state rs ♯ X)
            ((sReifier_state (rs !!! i) ♯ X) * (gState_rest i rs ♯ X))%type.
  Proof.
    revert i. induction rs as [|n r rs]=>i.
    { inversion i. }
    inv_fin i; simpl.
    { apply iso_ofe_refl. }
    intros i.
    specialize (IHrs i).
    unshelve esplit.
    - simple refine (λne xr, let sr := ofe_iso_1 IHrs (xr.2) in
                             (sr.1,(xr.1,sr.2))).
      solve_proper.
    - simple refine (λne sxr, let r' := ofe_iso_2 IHrs (sxr.1,sxr.2.2) in
                              (sxr.2.1, r')).
      solve_proper.
    - intros (s & x & rest). simpl. repeat f_equiv; rewrite ofe_iso_12//.
    - intros (x & rest). simpl. f_equiv.
      rewrite -surjective_pairing. apply ofe_iso_21.
  Defined.
  Definition gState_decomp {m} (i : fin m) {rs : gReifiers m} {X} `{!Cofe X} :
    (gReifiers_state rs ♯ X) -n> ((sReifier_state (rs !!! i) ♯ X) * (gState_rest i rs ♯ X))%type
    := ofe_iso_1 (gState_decomp' i rs).
  Program Definition gState_recomp {m} {i : fin m} {rs : gReifiers m} {X} `{!Cofe X} :
    (gState_rest i rs ♯ X) -n> (sReifier_state (rs !!! i) ♯ X) -n> (gReifiers_state rs ♯ X)
    := λne rest st, ofe_iso_2 (gState_decomp' i rs) (st, rest).
  Solve All Obligations with solve_proper_please.

  Lemma gState_decomp_recomp {m} (i : fin m) {rs : gReifiers m} {X} `{!Cofe X}
    (σ : sReifier_state (rs !!! i) ♯ X) rest :
    gState_decomp i (gState_recomp rest σ) ≡ (σ, rest).
  Proof. rewrite ofe_iso_12. reflexivity. Qed.
  Lemma gState_recomp_decomp {m} (i : fin m) {rs : gReifiers m} {X} `{!Cofe X}
    (σ : sReifier_state (rs !!! i) ♯ X) rest fs :
      gState_decomp i fs ≡ (σ, rest) →
      gState_recomp rest σ ≡ fs.
  Proof.
    unfold gState_recomp. simpl.
    intros <-. rewrite ofe_iso_21//.
  Qed.
  Opaque gState_recomp gState_decomp.

  Program Definition gReifiers_re {n} (rs : gReifiers n) {X} `{!Cofe X}
    (op : opid (gReifiers_ops rs)) :
    (Ins (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X) -n>
      optionO ((Outs (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X))
    :=  λne xst,
      let  i := projT1 op in
      let op' := projT2 op in
      let x := xst.1 in
      let st := xst.2 in
      let fs := gState_decomp i st in
      let σ := fs.1 in
      let rest := fs.2 in
      let rx := sReifier_re (rs !!! i) op' (x, σ) in
      optionO_map (prodO_map idfun (gState_recomp rest)) rx.
  Next Obligation. solve_proper_please. Qed.

  (** We can turn a collection of reifiers into a single reifier *)
  Definition gReifiers_sReifier {n} (rs : gReifiers n) : sReifier :=
    {| sReifier_ops := gReifiers_ops rs;
       sReifier_state := gReifiers_state rs;
       sReifier_re := @gReifiers_re n rs;
    |}.

  (* XXX : move *)
  Global Instance optionO_map_proper (A B : ofe) :
    Proper ((≡) ==> (≡)) (@optionO_map A B).
  Proof. solve_proper. Qed.

  Lemma gReifiers_re_idx {n}  (i : fin n) (rs : gReifiers n)
    {X} `{!Cofe X} (op : opid (sReifier_ops (rs !!! i)))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (σ : sReifier_state (rs !!! i) ♯ X) (rest : gState_rest i rs ♯ X) :
    gReifiers_re rs (existT i op) (x, gState_recomp rest σ) ≡
      optionO_map (prodO_map idfun (gState_recomp rest))
           (sReifier_re (rs !!! i) op (x,σ)).
  Proof.
    unfold gReifiers_re. cbn-[prodO_map optionO_map].
    f_equiv; last repeat f_equiv.
    - eapply optionO_map_proper.
      intros [x1 x2]; simpl. f_equiv.
      f_equiv. f_equiv.
      rewrite gState_decomp_recomp//.
    - rewrite gState_decomp_recomp//.
  Qed.

  Class subReifier {n} (r : sReifier) (rs : gReifiers n) :=
    { sR_idx : fin n;
      sR_ops :: subEff (sReifier_ops r) (sReifier_ops (rs !!! sR_idx));
      sR_state  {X} `{!Cofe X} :
        ofe_iso (sReifier_state r ♯ X) (sReifier_state (rs !!! sR_idx) ♯ X);
      sR_re m {X} `{!Cofe X} (op : opid (sReifier_ops r))
        (x : Ins (sReifier_ops _ op) ♯ X)
        (y : Outs (sReifier_ops _ op) ♯ X)
        (s1 s2 : sReifier_state r ♯ X) :
        sReifier_re r op (x, s1) ≡{m}≡ Some (y, s2) →
        sReifier_re (rs !!! sR_idx) (subEff_opid op)
          (subEff_conv_ins x, ofe_iso_1 sR_state s1) ≡{m}≡
          Some (subEff_conv_outs y, ofe_iso_1 sR_state s2) }.

  #[global] Instance subReifier_here {n} (r : sReifier) (rs : gReifiers n) :
    subReifier r (gReifiers_cons r rs).
  Proof.
    simple refine ({| sR_idx := 0%fin |}).
    - simpl. intros. apply iso_ofe_refl.
    - intros X ? op x y s1 s2.
      simpl. eauto.
  Defined.
  #[global] Instance subReifier_there {n} (r r' : sReifier) (rs : gReifiers n) :
    subReifier r rs →
    subReifier r (gReifiers_cons r' rs).
  Proof.
    intros SR.
    simple refine ({| sR_idx := FS sR_idx |}).
    - simpl. intros. apply sR_state.
    - intros X ? op x y s1 s2.
      simpl. apply sR_re.
  Defined.

  #[local] Definition subR_op {n} {r : sReifier} {rs : gReifiers n} `{!subReifier r rs} :
    opid (sReifier_ops r) → opid (gReifiers_ops rs).
  Proof.
    intros op.
    simpl.
    refine (existT sR_idx (subEff_opid op)).
  Defined.
  Definition subR_conv_state {n} {r : sReifier} {rs : gReifiers n} `{!subReifier r rs}
    {X} `{!Cofe X}:
    (sReifier_state r ♯ X) -n> (sReifier_state (rs !!! sR_idx) ♯ X) :=
    ofe_iso_1 sR_state.
  #[export] Instance subReifier_subEff {n} {r : sReifier} {rs : gReifiers n} `{!subReifier r rs} :
    subEff (sReifier_ops r) (gReifiers_ops rs).
  Proof.
    simple refine {| subEff_opid := subR_op |}.
    - intros op X ?. simpl.
      apply subEff_ins.
    - intros op X ?. simpl.
      apply subEff_outs.
  Defined.

  Lemma subReifier_reify_idx {n} (r : sReifier) (rs : gReifiers n)
    `{!subReifier r rs} {X} `{!Cofe X} (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (y : Outs (sReifier_ops _ op) ♯ X)
    (s1 s2 : sReifier_state r ♯ X) :
        sReifier_re r op (x, s1) ≡ Some (y, s2) →
        sReifier_re (rs !!! sR_idx) (subEff_opid op)
          (subEff_conv_ins x, ofe_iso_1 sR_state s1) ≡
          Some (subEff_conv_outs y, ofe_iso_1 sR_state s2).
  Proof.
    intros Hx. apply equiv_dist=>m.
    apply sR_re. by apply equiv_dist.
  Qed.
  
  Lemma subReifier_reify {n} (r : sReifier)
    (rs : gReifiers n) `{!subReifier r rs} {X} `{!Cofe X}
    (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X) (y : Outs (sReifier_ops _ op) ♯ X)
    (σ σ' : sReifier_state r ♯ X) (rest : gState_rest sR_idx rs ♯ X) :
    sReifier_re r op (x,σ) ≡ Some (y, σ') →
    gReifiers_re rs (subEff_opid op)
      (subEff_conv_ins x, gState_recomp rest (subR_conv_state σ))
      ≡ Some (subEff_conv_outs y, gState_recomp rest (subR_conv_state σ')).
  Proof.
    intros Hre.
    eapply subReifier_reify_idx in Hre.
    rewrite gReifiers_re_idx//.
    rewrite Hre. simpl. reflexivity.
  Qed.

  (************************************************************************)

  Context {n : nat} (rs : gReifiers n).
  Notation F := (gReifiers_ops rs).
  Notation stateF := (gReifiers_state rs).
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
    - simple refine (let ns := gReifiers_re rs op (oFunctor_map _ (inlO,fstO) i, s) in _).
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
    sumO (sumO (sumO (sumO natO errorO) (laterO (stateM -n> stateM))) (laterO stateM))
      (sigTO (λ op : opid F, prodO (oFunctor_apply (Ins (F op)) stateM) (oFunctor_apply (Outs (F op)) stateM -n> laterO stateM))).
  Proof. simple refine (λne d, inl (inl (inl (inr (RuntimeErr))))). Qed.

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
    gReifiers_re rs op (i,σ) ≡{m}≡ Some (o,σ') →
    reify (Vis op i k) σ ≡{m}≡ (σ', Tau $ k o).
  Proof.
    intros Hst.
    trans (reify_vis op
             (oFunctor_map _ (sumO_rec idfun unreify,prod_in idfun reify) i)
             (laterO_map (prod_in idfun reify) ◎ k ◎ (oFunctor_map _ (prod_in idfun reify,sumO_rec idfun unreify)))
             σ).
    { f_equiv. rewrite IT_rec1_vis//. }
    Opaque prod_in. simpl.
    pose (r := (gReifiers_re rs op
      (oFunctor_map (Ins (F op)) (inlO, fstO)
                    (oFunctor_map (Ins (F op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold r.
    assert (r ≡ gReifiers_re rs op (i,σ)) as Hr'.
    { unfold r. f_equiv. f_equiv.
      rewrite -oFunctor_map_compose.
      etrans; last by apply oFunctor_map_id.
      repeat f_equiv; intro; done. }
    assert (r ≡{m}≡ Some (o,σ')) as Hr.
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
    gReifiers_re rs op (i,σ) ≡ Some (o,σ') →
    reify (Vis op i k) σ ≡ (σ', Tau $ k o).
  Proof.
    intros H. apply equiv_dist=>m.
    apply reify_vis_dist.
    by apply equiv_dist.
  Qed.

  Lemma reify_vis_None op i k σ :
    gReifiers_re rs op (i,σ) ≡ None →
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
    pose (r := (gReifiers_re rs op
      (oFunctor_map (Ins (F op)) (inlO, fstO)
                    (oFunctor_map (Ins (F op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
    fold r.
    assert (r ≡ gReifiers_re rs op (i,σ)) as Hr'.
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
    destruct (gReifiers_re rs op (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
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
    destruct (gReifiers_re rs op (i,σ1)) as [[o σ2']|] eqn:Hre; last first.
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
    destruct (gReifiers_re rs op (x, σ)) as [[o σ'']|] eqn:Hre; last first.
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
Arguments reify {n} rs.
