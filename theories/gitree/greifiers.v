From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify.


Section greifiers.
  #[local] Open Scope type.

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
    gReifiers_state rs ♯ X ≃
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
    - simple refine (λne sxr, let r' := IHrs^-1 (sxr.1,sxr.2.2) in
                              (sxr.2.1, r')).
      solve_proper.
    - intros (s & x & rest). simpl. repeat f_equiv; rewrite ofe_iso_12//.
    - intros (x & rest). simpl. f_equiv.
      rewrite -surjective_pairing. apply ofe_iso_21.
  Defined.
  Definition gState_decomp {m} (i : fin m) {rs : gReifiers m} {X} `{!Cofe X} :
    (gReifiers_state rs ♯ X) -n> ((sReifier_state (rs !!! i) ♯ X) * (gState_rest i rs ♯ X))%type
    := gState_decomp' i rs.
  Program Definition gState_recomp {m} {i : fin m} {rs : gReifiers m} {X} `{!Cofe X} :
    (gState_rest i rs ♯ X) -n> (sReifier_state (rs !!! i) ♯ X) -n> (gReifiers_state rs ♯ X)
    := λne rest st, (gState_decomp' i rs)^-1 (st, rest).
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
    (Ins (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X) * ((Outs (gReifiers_ops rs op) ♯ X) -n> laterO X) -n>
      optionO (laterO X * (gReifiers_state rs ♯ X))
    :=  λne xst,
      let  i := projT1 op in
      let op' := projT2 op in
      let a := xst.1.1 in
      let b := xst.1.2 in
      let c := xst.2 in
      let fs := gState_decomp i b in
      let σ := fs.1 in
      let rest := fs.2 in
      let rx := sReifier_re (rs !!! i) op' (a, σ, c) in
      optionO_map (prodO_map idfun (gState_recomp rest)) rx.
  Next Obligation. solve_proper_please. Qed.

  (** We can turn a collection of reifiers into a single reifier *)
  Definition gReifiers_sReifier {n} (rs : gReifiers n) : sReifier :=
    {| sReifier_ops := gReifiers_ops rs;
       sReifier_state := gReifiers_state rs;
       sReifier_re := @gReifiers_re n rs;
    |}.

  Lemma gReifiers_re_idx {n} (i : fin n) (rs : gReifiers n)
    {X} `{!Cofe X} (op : opid (sReifier_ops (rs !!! i)))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (σ : sReifier_state (rs !!! i) ♯ X)
    (κ : (Outs (sReifier_ops (rs !!! i) op) ♯ X -n> laterO X))
    (rest : gState_rest i rs ♯ X) :
    gReifiers_re rs (existT i op) (x, gState_recomp rest σ, κ) ≡
      optionO_map (prodO_map idfun (gState_recomp rest))
      (sReifier_re (rs !!! i) op (x, σ, κ)).
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
      sR_state {X} `{!Cofe X} :
      sReifier_state r ♯ X ≃ sReifier_state (rs !!! sR_idx) ♯ X;
      sR_re (m : nat) {X} `{!Cofe X} (op : opid (sReifier_ops r))
        (x : Ins (sReifier_ops r op) ♯ X)
        (y : laterO X)
        (s1 s2 : sReifier_state r ♯ X)
        (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X)) :
      sReifier_re r op (x, s1, k) ≡{m}≡ Some (y, s2) →
      sReifier_re (rs !!! sR_idx) (subEff_opid op)
        (subEff_ins x, sR_state s1, k ◎ (subEff_outs ^-1)) ≡{m}≡
        Some (y, sR_state s2)
    }.

  #[global] Instance subReifier_here {n} (r : sReifier) (rs : gReifiers n) :
    subReifier r (gReifiers_cons r rs).
  Proof.
    simple refine ({| sR_idx := 0%fin |}).
    - simpl. apply subEff_id.
    - simpl. intros. apply iso_ofe_refl.
    - intros X ? op x y ? s1 s2 k HEQ; simpl.
      unfold ofe_iso_1'; simpl.
      rewrite ccompose_id_r HEQ.
      reflexivity.
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
    (* (y : Outs (sReifier_ops _ op) ♯ X) *)
    (y : laterO X)
    (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
    (s1 s2 : sReifier_state r ♯ X) :
    sReifier_re r op (x, s1, k) ≡ Some (y, s2) →
      sReifier_re (rs !!! sR_idx) (subEff_opid op)
        (subEff_ins x, sR_state s1, k ◎ (subEff_outs ^-1)) ≡
        Some (y, sR_state s2).
  Proof.
    intros Hx. apply equiv_dist=>m.
    apply sR_re. by apply equiv_dist.
  Qed.

  Lemma subReifier_reify {n} (r : sReifier)
    (rs : gReifiers n) `{!subReifier r rs} {X} `{!Cofe X}
    (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X) (y : laterO X)
    (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
    (σ σ' : sReifier_state r ♯ X) (rest : gState_rest sR_idx rs ♯ X) :
    sReifier_re r op (x, σ, k) ≡ Some (y, σ') →
    gReifiers_re rs (subEff_opid op)
      (subEff_ins x, gState_recomp rest (sR_state σ), k ◎ (subEff_outs ^-1))
      ≡ Some (y, gState_recomp rest (sR_state σ')).
  Proof.
    intros Hre.
    eapply subReifier_reify_idx in Hre.
    rewrite gReifiers_re_idx//.
    rewrite Hre. simpl.
    do 3 f_equiv.
  Qed.

  (** Lemma for reasoning internally in iProp *)
  Context `{!invGS_gen hlc Σ}.
  Notation iProp := (iProp Σ).
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Notation sr := (gReifiers_sReifier rs).

  Lemma reify_vis_eqI {A} `{!Cofe A} op i k o σ σ' :
    (gReifiers_re rs op (i, σ, k) ≡ Some (o,σ') ⊢@{iProp} reify sr (Vis op i k : IT _ A) σ ≡ (σ', Tau $ o))%I.
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros H. apply reify_vis_dist. exact H.
  Qed.

  Lemma subReifier_reify_idxI (r : sReifier)
    `{!subReifier r rs} {X} `{!Cofe X} (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (y : laterO X)
    (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
    (s1 s2 : sReifier_state r ♯ X) :
        sReifier_re r op (x, s1, k) ≡ Some (y, s2) ⊢@{iProp}
        sReifier_re (rs !!! sR_idx) (subEff_opid op)
          (subEff_ins x, sR_state s1, k ◎ (subEff_outs ^-1)) ≡
          Some (y, sR_state s2).
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros H.
    rewrite sR_re; last first.
    - rewrite H.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma subReifier_reifyI (r : sReifier)
    `{!subReifier r rs} {X} `{!Cofe X}
    (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X) (y : laterO X)
    (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
    (σ σ' : sReifier_state r ♯ X) (rest : gState_rest sR_idx rs ♯ X) :
    sReifier_re r op (x,σ, k) ≡ Some (y, σ') ⊢@{iProp}
    gReifiers_re rs (subEff_opid op)
      (subEff_ins x, gState_recomp rest (sR_state σ), k ◎ (subEff_outs ^-1))
      ≡ Some (y, gState_recomp rest (sR_state σ')).
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros He.
    eapply sR_re in He.
    rewrite gReifiers_re_idx//.
    rewrite He. simpl.
    reflexivity.
  Qed.

End greifiers.
