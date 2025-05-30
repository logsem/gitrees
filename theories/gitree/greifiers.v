From iris.algebra Require Import list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify.

Section greifiers_generic.
  #[local] Open Scope type.
  Context (a : is_ctx_dep).
  Notation sReifier := (sReifier a).

  (** Global reifiers: a collection of reifiers *)
  Inductive gReifiers : nat → Type :=
  | gReifiers_nil : gReifiers 0
  | gReifiers_cons {n} : sReifier → gReifiers n → gReifiers (S n)
  .

  Definition grs_O_inv (P : gReifiers 0 -> Type) (H : P gReifiers_nil)
    (v : gReifiers 0) : P v :=
    match v with
    | gReifiers_nil => H
    | gReifiers_cons sR v => fun devil => False_ind (@IDProp) devil
    end.

  Definition grs_S_inv {n} (P : gReifiers (S n) → Type)
    (Hcons : ∀ sR v, P (gReifiers_cons sR v)) v : P v.
  Proof.
    revert P Hcons.
    refine match v with gReifiers_nil => tt
                   | gReifiers_cons sR v => λ P Hcons, Hcons sR v end.
  Defined.

  #[global] Instance gReifiers_lookup_total
    : ∀ m, LookupTotal (fin m) sReifier (gReifiers m) :=
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

End greifiers_generic.

Section greifiers.
  #[local] Open Scope type.

  Program Definition gReifiers_re_ctx_indep {n} (rs : gReifiers NotCtxDep n) {X} `{!Cofe X}
    (op : opid (gReifiers_ops NotCtxDep rs)) :
    (Ins (gReifiers_ops NotCtxDep rs op) ♯ X) * (gReifiers_state NotCtxDep rs ♯ X) -n>
      optionO ((Outs (gReifiers_ops NotCtxDep rs op) ♯ X) * (gReifiers_state NotCtxDep rs ♯ X) * listO (laterO X))
    :=  λne xst,
      let  i := projT1 op in
      let op' := projT2 op in
      let x := xst.1 in
      let st := xst.2 in
      let fs := gState_decomp NotCtxDep i st in
      let σ := fs.1 in
      let rest := fs.2 in
      let rx := sReifier_re (rs !!! i) op' (x, σ) in
      optionO_map (prodO_map (prodO_map idfun (gState_recomp NotCtxDep rest)) idfun) rx.
  Next Obligation. solve_proper_please. Qed.

  Program Definition gReifiers_re_ctx_dep {n} (rs : gReifiers CtxDep n) {X} `{!Cofe X}
    (op : opid (gReifiers_ops CtxDep rs)) :
    (Ins (gReifiers_ops CtxDep rs op) ♯ X) * (gReifiers_state CtxDep rs ♯ X)
    * ((Outs (gReifiers_ops CtxDep rs op) ♯ X) -n> laterO X) -n>
      optionO (laterO X * (gReifiers_state CtxDep rs ♯ X) * listO (laterO X))
    :=  λne xst,
      let  i := projT1 op in
      let op' := projT2 op in
      let a := xst.1.1 in
      let b := xst.1.2 in
      let c := xst.2 in
      let fs := gState_decomp CtxDep i b in
      let σ := fs.1 in
      let rest := fs.2 in
      let rx := sReifier_re (rs !!! i) op' (a, σ, c) in
      optionO_map (prodO_map (prodO_map idfun (gState_recomp CtxDep rest)) idfun) rx.
  Next Obligation. solve_proper_please. Qed.

  Program Definition gReifiers_re_type {n}
    (a : is_ctx_dep) (rs : gReifiers a n) {X} `{!Cofe X}
    (op : opid (gReifiers_ops a rs)) : ofe :=
    match a with
    | CtxDep =>
        prodO (prodO (Ins (gReifiers_ops a rs op) ♯ X) (gReifiers_state a rs ♯ X))
          (Outs (gReifiers_ops a rs op) ♯ X -n> laterO X) -n>
          optionO (prodO (prodO (laterO X) (gReifiers_state a rs ♯ X)) (listO (laterO X)))
    | NotCtxDep =>
        prodO (Ins (gReifiers_ops a rs op) ♯ X) (gReifiers_state a rs ♯ X) -n>
          optionO (prodO (prodO (Outs (gReifiers_ops a rs op) ♯ X) (gReifiers_state a rs ♯ X)) (listO (laterO X)))
    end.

  Program Definition gReifiers_re {n} (a : is_ctx_dep) (rs : gReifiers a n)
    {X} `{!Cofe X}
    (op : opid (gReifiers_ops a rs)) :
    @gReifiers_re_type n a rs X _ op.
  Proof.
    destruct a.
    - apply gReifiers_re_ctx_dep.
    - apply gReifiers_re_ctx_indep.
  Defined.

  (** We can turn a collection of reifiers into a single reifier *)
  Program Definition gReifiers_sReifier {n} (a : is_ctx_dep) (rs : gReifiers a n)
    : sReifier a :=
    {| sReifier_ops := gReifiers_ops a rs;
      sReifier_state := gReifiers_state a rs;
      sReifier_re X _ op := _;
    |}.
  Next Obligation.
    intros n [|] rs X ? op.
    - pose proof (@gReifiers_re n CtxDep rs X _ op).
      simpl in *.
      apply (@gReifiers_re n CtxDep rs X _ op).
    - apply (@gReifiers_re n NotCtxDep rs X _ op).
  Defined.

  Lemma gReifiers_re_idx_ctx_dep {n} (i : fin n) (rs : gReifiers CtxDep n)
    {X} `{!Cofe X} (op : opid (sReifier_ops (rs !!! i)))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (σ : sReifier_state (rs !!! i) ♯ X)
    (rest : gState_rest CtxDep i rs ♯ X)
    (κ : (Outs (sReifier_ops (rs !!! i) op) ♯ X -n> laterO X)) :
    gReifiers_re CtxDep rs (existT i op) (x, gState_recomp CtxDep rest σ, κ) ≡
      optionO_map (prodO_map (prodO_map idfun (gState_recomp CtxDep rest)) idfun)
      (sReifier_re (rs !!! i) op (x, σ, κ)).
  Proof.
    unfold gReifiers_re. cbn-[prodO_map optionO_map].
    f_equiv; last repeat f_equiv.
    - eapply optionO_map_proper.
      intros [[x1 x3] x2]; simpl. do 2 f_equiv.
      rewrite gState_decomp_recomp//.
    - rewrite gState_decomp_recomp//.
  Qed.

  Lemma gReifiers_re_idx_ctx_indep {n} (i : fin n) (rs : gReifiers NotCtxDep n)
    {X} `{!Cofe X} (op : opid (sReifier_ops (rs !!! i)))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (σ : sReifier_state (rs !!! i) ♯ X)
    (rest : gState_rest NotCtxDep i rs ♯ X) :
    gReifiers_re NotCtxDep rs (existT i op) (x, gState_recomp NotCtxDep rest σ) ≡
      optionO_map (prodO_map (prodO_map idfun (gState_recomp NotCtxDep rest)) idfun)
      (sReifier_re (rs !!! i) op (x, σ)).
  Proof.
    unfold gReifiers_re. cbn-[prodO_map optionO_map].
    f_equiv; last repeat f_equiv.
    - eapply optionO_map_proper.
      intros [[x1 x3] x2]; simpl. do 2 f_equiv.
      f_equiv. f_equiv.
      rewrite gState_decomp_recomp//.
    - rewrite gState_decomp_recomp//.
  Qed.

  Program Definition gReifiers_re_idx_type {n} a (i : fin n) (rs : gReifiers a n)
    {X} `{!Cofe X} (op : opid (sReifier_ops (rs !!! i)))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (σ : sReifier_state (rs !!! i) ♯ X)
    (rest : gState_rest a i rs ♯ X) :
    Type.
  Proof.
    destruct a.
    - apply (∀ (κ : (Outs (sReifier_ops (rs !!! i) op) ♯ X -n> laterO X)),
               gReifiers_re CtxDep rs (existT i op) (x, gState_recomp CtxDep rest σ, κ) ≡
                 optionO_map (prodO_map (prodO_map idfun (gState_recomp CtxDep rest)) idfun)
                 (sReifier_re (rs !!! i) op (x, σ, κ))).
    - apply (gReifiers_re NotCtxDep rs (existT i op) (x, gState_recomp NotCtxDep rest σ) ≡
               optionO_map (prodO_map (prodO_map idfun (gState_recomp NotCtxDep rest)) idfun)
               (sReifier_re (rs !!! i) op (x, σ))).
  Defined.

  Lemma gReifiers_re_idx {n} a (i : fin n) (rs : gReifiers a n)
    {X} `{!Cofe X} (op : opid (sReifier_ops (rs !!! i)))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (σ : sReifier_state (rs !!! i) ♯ X)
    (rest : gState_rest a i rs ♯ X) : gReifiers_re_idx_type a i rs op x σ rest.
  Proof.
    destruct a.
    - intros κ. apply gReifiers_re_idx_ctx_dep.
    - apply gReifiers_re_idx_ctx_indep.
  Qed.

  Program Definition sR_re_type {n}
    {X} `{!Cofe X} (a : is_ctx_dep) (r : sReifier a) (rs : gReifiers a n)
    (sR_idx : fin n)
    (sR_ops : subEff (sReifier_ops r) (sReifier_ops (rs !!! sR_idx)))
    (sR_state : sReifier_state r ♯ X ≃ sReifier_state (rs !!! sR_idx) ♯ X)
    (m : nat) (op : opid (sReifier_ops r)) : Type.
  Proof.
    destruct a.
    - apply (∀ (x : Ins (sReifier_ops r op) ♯ X)
               (y : laterO X)
               (s1 s2 : sReifier_state r ♯ X)
               (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X)) th,
               sReifier_re r op (x, s1, k) ≡{m}≡ Some (y, s2, th) →
               @sReifier_re CtxDep (rs !!! sR_idx) _ _ (subEff_opid op)
                 (subEff_ins x, sR_state s1, k ◎ (subEff_outs ^-1)) ≡{m}≡
                 Some (y, sR_state s2, th)).
    - apply (∀ (x : Ins (sReifier_ops _ op) ♯ X)
               (y : Outs (sReifier_ops _ op) ♯ X)
               (s1 s2 : sReifier_state r ♯ X) th,
               sReifier_re r op (x, s1) ≡{m}≡ Some (y, s2, th) →
               @sReifier_re NotCtxDep (rs !!! sR_idx) _ _ (subEff_opid op)
                 (subEff_ins x, sR_state s1) ≡{m}≡
                 Some (subEff_outs y, sR_state s2, th)).
  Defined.

  Class subReifier {n} {a : is_ctx_dep} (r : sReifier a) (rs : gReifiers a n) :=
    { sR_idx : fin n;
      sR_ops :: subEff (sReifier_ops r) (sReifier_ops (rs !!! sR_idx));
      sR_state {X} `{!Cofe X} :
      sReifier_state r ♯ X ≃ sReifier_state (rs !!! sR_idx) ♯ X;
      sR_re (m : nat) {X} `{!Cofe X} (op : opid (sReifier_ops r))
      : sR_re_type a r rs sR_idx sR_ops (@sR_state X _) m op
    }.

  #[global] Instance subReifier_here {n} {a : is_ctx_dep}
    (r : sReifier a) (rs : gReifiers a n) :
    subReifier r (gReifiers_cons a r rs).
  Proof.
    simple refine ({| sR_idx := 0%fin |}).
    - simpl. apply subEff_id.
    - simpl. intros. apply iso_ofe_refl.
    - destruct a.
      + intros X ? op x y ? s1 s2 k th HEQ; simpl.
        unfold ofe_iso_1'; simpl.
        rewrite ccompose_id_r HEQ.
        reflexivity.
      + intros X ? op x y o s2 s3 th.
        simpl. eauto.
  Defined.

  #[global] Instance subReifier_there {n} {a : is_ctx_dep}
    (r r' : sReifier a) (rs : gReifiers a n) :
    subReifier r rs →
    subReifier r (gReifiers_cons a r' rs).
  Proof.
    intros SR.
    simple refine ({| sR_idx := FS sR_idx |}).
    - simpl. intros. apply sR_state.
    - destruct a.
      + intros ? X ? op x y s1 s2 k th.
        simpl. intros.
        pose proof (@sR_re n CtxDep r rs _ m X _ op) as G.
        simpl in G.
        by apply G.
      + intros ? X ? op x y s1 s2 th.
        simpl. intros.
        pose proof (@sR_re n NotCtxDep r rs _ m X _ op) as G.
        simpl in G.
        by apply G.
  Defined.

  #[local] Definition subR_op {n} {a : is_ctx_dep}
    {r : sReifier a} {rs : gReifiers a n} `{!subReifier r rs} :
    opid (sReifier_ops r) → opid (gReifiers_ops a rs).
  Proof.
    intros op.
    simpl.
    refine (existT sR_idx (subEff_opid op)).
  Defined.

  #[export] Instance subReifier_subEff {n} {a : is_ctx_dep}
    {r : sReifier a} {rs : gReifiers a n} `{!subReifier r rs} :
    subEff (sReifier_ops r) (gReifiers_ops a rs).
  Proof.
    simple refine {| subEff_opid := subR_op |}.
    - intros op X ?. simpl.
      apply subEff_ins.
    - intros op X ?. simpl.
      apply subEff_outs.
  Defined.

  #[export] Instance reifier_coercion_subEff {sz} r (rs : gReifiers CtxDep sz)
    `{H : !subReifier (sReifier_NotCtxDep_CtxDep r) rs} :
    subEff (sReifier_ops r) (gReifiers_ops _ rs) | 100.
  Proof.
      simple refine
               {| subEff_opid (op : opid (sReifier_ops (sReifier_NotCtxDep_CtxDep r)))
                 := subEff_opid op |}.
      - intros. apply subEff_ins.
      - intros. apply subEff_outs.
  Defined.

  Program Definition subReifier_reify_idx_type {n}
    (a : is_ctx_dep) (r : sReifier a) (rs : gReifiers a n)
    `{!subReifier r rs} X `{!Cofe X} (op : opid (sReifier_ops r)) : Type.
  Proof.
    destruct a.
    - apply (∀ (x : Ins (sReifier_ops r op) ♯ X)
               (y : laterO X)
               (s1 s2 : sReifier_state r ♯ X)
               (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X)) th,
               sReifier_re r op (x, s1, k) ≡ Some (y, s2, th) →
               @sReifier_re CtxDep (rs !!! sR_idx) _ _ (subEff_opid op)
                 (subEff_ins x, sR_state s1, k ◎ (subEff_outs ^-1)) ≡
                 Some (y, sR_state s2, th)).
    - apply (∀ (x : Ins (sReifier_ops _ op) ♯ X)
               (y : Outs (sReifier_ops _ op) ♯ X)
               (s1 s2 : sReifier_state r ♯ X) th,
               sReifier_re r op (x, s1) ≡ Some (y, s2, th) →
               @sReifier_re NotCtxDep (rs !!! sR_idx) _ _ (subEff_opid op)
                 (subEff_ins x, sR_state s1) ≡
                 Some (subEff_outs y, sR_state s2, th)).
  Defined.

  Lemma subReifier_reify_idx {n} {a : is_ctx_dep}
    (r : sReifier a) (rs : gReifiers a n)
    `{!subReifier r rs} {X} `{!Cofe X} (op : opid (sReifier_ops r))
    : subReifier_reify_idx_type a r rs X op.
  Proof.
    destruct a.
    - intros Hx. intros. apply equiv_dist=>m.
      pose proof (@sR_re n CtxDep r rs _ m X _ op Hx y s1 s2 k) as G.
      simpl in G.
      rewrite G; first done.
      by apply equiv_dist.
    - intros Hx. intros. apply equiv_dist=>m.
      pose proof (@sR_re n NotCtxDep r rs _ m X _ op Hx y s1 s2) as G.
      simpl in G.
      rewrite G; first done.
      by apply equiv_dist.
  Qed.

  Program Definition subReifier_reify_type {n} (a : is_ctx_dep) (r : sReifier a)
    (rs : gReifiers a n) `{!subReifier r rs} X `{!Cofe X}
    (op : opid (sReifier_ops r)) : Type.
  Proof.
    destruct a.
    - apply (∀ (x : Ins (sReifier_ops _ op) ♯ X) (y : laterO X)
               (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
               (σ σ' : sReifier_state r ♯ X) (rest : gState_rest CtxDep sR_idx rs ♯ X) th,
               sReifier_re r op (x, σ, k) ≡ Some (y, σ', th) →
               gReifiers_re CtxDep rs (subEff_opid op)
                 (subEff_ins x, gState_recomp CtxDep rest (sR_state σ), k ◎ (subEff_outs ^-1))
                 ≡ Some (y, gState_recomp CtxDep rest (sR_state σ'), th)).
    - apply (∀ (x : Ins (sReifier_ops _ op) ♯ X) (y : Outs (sReifier_ops _ op) ♯ X)
               (σ σ' : sReifier_state r ♯ X) (rest : gState_rest NotCtxDep sR_idx rs ♯ X) th,
               sReifier_re r op (x,σ) ≡ Some (y, σ', th) →
               gReifiers_re NotCtxDep rs (subEff_opid op)
                 (subEff_ins x, gState_recomp NotCtxDep rest (sR_state σ))
                 ≡ Some (subEff_outs y, gState_recomp NotCtxDep rest (sR_state σ'), th)).
  Defined.

  Lemma subReifier_reify {n} {a : is_ctx_dep} (r : sReifier a)
    (rs : gReifiers a n) `{!subReifier r rs} {X} `{!Cofe X}
    (op : opid (sReifier_ops r)) : subReifier_reify_type a r rs X op.
  Proof.
    destruct a.
    - simpl.
      intros x y k σ σ' H th Hre.
      pose proof (@subReifier_reify_idx n CtxDep r rs _ X _ op x y σ σ' k th Hre) as J; clear Hre.
      simpl in J.
      pose proof (@gReifiers_re_idx n CtxDep sR_idx rs X _ (subEff_opid op)) as J'.
      simpl in J'.
      rewrite J'; clear J'.
      transitivity (prod_map (prod_map (λ x0 : laterO X, x0)
                      (λ st : sReifier_state (rs !!! sR_idx) ♯ X,
                          (gState_decomp' CtxDep sR_idx rs ^-1) (st, H))) idfun <$>
                      (Some (y, sR_state σ', th))).
      + unfold prod_map.
        rewrite option_fmap_proper; [reflexivity | intros ??? | apply J].
        f_equiv; last (simpl; by f_equiv).
        f_equiv; first (by do 2 f_equiv).
        by do 4 f_equiv.
      + simpl; reflexivity.
    - simpl.
      intros x y σ σ' rest th Hre.
      pose proof (@subReifier_reify_idx n NotCtxDep r rs _ X _ op x y σ σ' th Hre)
        as J; clear Hre.
      simpl in J.
      pose proof (@gReifiers_re_idx n NotCtxDep sR_idx rs X _ (subEff_opid op))
        as J'.
      simpl in J'.
      rewrite J'; clear J'.
      transitivity (prod_map (prod_map (λ x0 : Outs (sReifier_ops (rs !!! sR_idx)
                                             (subEff_opid op)) ♯ X, x0)
                      (λ st : sReifier_state (rs !!! sR_idx) ♯ X,
                          (gState_decomp' NotCtxDep sR_idx rs ^-1) (st, rest))) idfun <$>
                      (Some (subEff_outs y, sR_state σ', th))).
      + unfold prod_map.
        rewrite option_fmap_proper; [reflexivity | intros ??? | apply J].
        f_equiv; last (simpl; by f_equiv).
        f_equiv; first (by do 2 f_equiv).
        by do 4 f_equiv.
      + simpl; reflexivity.
  Qed.

  (** Lemma for reasoning internally in iProp *)
  Context `{!invGS_gen hlc Σ}.
  Notation iProp := (iProp Σ).
  Context {sz : nat}.
  Notation sr a rs := (gReifiers_sReifier a rs).

  Lemma reify_vis_eqI_ctx_dep (rs : gReifiers CtxDep sz)
    {A} `{!Cofe A} op i k o σ σ' th :
    (gReifiers_re CtxDep rs op (i, σ, k) ≡ Some (o,σ',th)
     ⊢@{iProp} reify (sr CtxDep rs) (Vis op i k : IT _ A) σ ≡ (σ', Tau $ o, listO_map Tau th))%I.
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros H. apply reify_vis_dist_ctx_dep. exact H.
  Qed.

  Lemma reify_vis_eqI_ctx_indep (rs : gReifiers NotCtxDep sz)
    {A} `{!Cofe A} op i k o σ σ' th :
    (gReifiers_re NotCtxDep rs op (i, σ) ≡ Some (o,σ',th)
     ⊢@{iProp} reify (sr NotCtxDep rs) (Vis op i k : IT _ A) σ ≡ (σ', Tau $ k o, listO_map Tau th))%I.
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros H. apply reify_vis_dist_ctx_indep. exact H.
  Qed.

  Lemma subReifier_reify_idxI_ctx_dep (r : sReifier CtxDep)
    `{!@subReifier sz CtxDep r rs} {X} `{!Cofe X} (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (y : laterO X)
    (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
    (s1 s2 : sReifier_state r ♯ X) th :
    sReifier_re r op (x, s1, k) ≡ Some (y, s2, th)
    ⊢@{iProp}
       sReifier_re  (rs !!! sR_idx) (subEff_opid op)
       (subEff_ins x, sR_state s1, k ◎ (subEff_outs ^-1)) ≡
       Some (y, sR_state s2, th).
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros H'.
    rewrite (@sR_re _ CtxDep); last first.
    - rewrite H'.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma subReifier_reify_idxI_ctx_indep (r : sReifier NotCtxDep)
    `{!@subReifier sz NotCtxDep r rs} {X} `{!Cofe X} (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X)
    (y : Outs (sReifier_ops _ op) ♯ X)
    (s1 s2 : sReifier_state r ♯ X) th :
    sReifier_re r op (x, s1) ≡ Some (y, s2, th)
    ⊢@{iProp}
       sReifier_re (rs !!! sR_idx) (subEff_opid op)
       (subEff_ins x, sR_state s1) ≡
       Some (subEff_outs y, sR_state s2, th).
  Proof.
    apply uPred.internal_eq_entails=>m.
    apply (@sR_re _ NotCtxDep).
  Qed.

  Lemma subReifier_reifyI_ctx_dep (r : sReifier CtxDep)
    `{!@subReifier sz CtxDep r rs} {X} `{!Cofe X}
    (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X) (y : laterO X)
    (k : (Outs (sReifier_ops r op) ♯ X -n> laterO X))
    (σ σ' : sReifier_state r ♯ X) (rest : gState_rest CtxDep sR_idx rs ♯ X) th :
    sReifier_re r op (x,σ, k) ≡ Some (y, σ', th)
    ⊢@{iProp}
       gReifiers_re CtxDep rs (subEff_opid op)
       (subEff_ins x, gState_recomp CtxDep rest (sR_state σ), k ◎ (subEff_outs ^-1))
       ≡ Some (y, gState_recomp CtxDep rest (sR_state σ'), th).
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros He.
    eapply (@sR_re _ CtxDep) in He.
    rewrite (gReifiers_re_idx CtxDep)//.
    rewrite He. simpl.
    reflexivity.
  Qed.

  Lemma subReifier_reifyI_ctx_indep (r : sReifier NotCtxDep)
    `{!@subReifier sz NotCtxDep r rs} {X} `{!Cofe X}
    (op : opid (sReifier_ops r))
    (x : Ins (sReifier_ops _ op) ♯ X) (y : Outs (sReifier_ops _ op) ♯ X)
    (σ σ' : sReifier_state r ♯ X) (rest : gState_rest NotCtxDep sR_idx rs ♯ X) th :
    sReifier_re r op (x,σ) ≡ Some (y, σ', th)
    ⊢@{iProp}
       gReifiers_re NotCtxDep rs (subEff_opid op)
       (subEff_ins x, gState_recomp NotCtxDep rest (sR_state σ))
       ≡ Some (subEff_outs y, gState_recomp NotCtxDep rest (sR_state σ'), th).
  Proof.
    apply uPred.internal_eq_entails=>m.
    intros He.
    eapply (@sR_re _ NotCtxDep) in He.
    pose proof (@gReifiers_re_idx sz NotCtxDep sR_idx rs X _ (subEff_opid op)
                  (subEff_ins x)) as J.
    simpl in J.
    simpl.
    rewrite J//; clear J.
    transitivity (prod_map (prod_map (λ x0 : Outs (sReifier_ops (rs !!! sR_idx)
                                           (subEff_opid op)) ♯ X, x0)
                    (λ st : sReifier_state (rs !!! sR_idx) ♯ X,
                        (gState_decomp' NotCtxDep sR_idx rs ^-1) (st, rest))) idfun <$>
                    (Some
                       (subEff_outs y, sR_state σ', th))).
    - unfold prod_map.
      rewrite option_fmap_ne; [reflexivity | intros ??? | apply He].
      f_equiv; last (simpl; by f_equiv).
      f_equiv; first (by do 2 f_equiv).
      by do 4 f_equiv.
    - simpl.
      reflexivity.
  Qed.

End greifiers.

Arguments gReifiers_cons {_ _}.
Arguments gReifiers_nil {_}.
Arguments gReifiers_ops {_ _}.
Arguments gReifiers_re {_ _}.
Arguments gState_rest {_ _}.
Arguments gState_recomp {_ _ _ _ _ _}.
Arguments gState_decomp {_ _} _ {_ _ _}.
Arguments gState_decomp' {_ _} _ {_ _ _}.
Arguments gReifiers_state {_ _}.
Arguments gReifiers_re_idx {_ _}.
Arguments gReifiers_re_idx_type {_ _}.
Arguments gReifiers_re_type {_ _}.
Arguments gReifiers_sReifier {_ _}.
