From iris.proofmode Require Import classes tactics.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core.

Section abstract_res.
  Variable (R : Type).
  Variable (Op : R → Type).
  Variable (In : forall {r : R}, Op r → oFunctor).
  Variable (Out : forall {r : R}, Op r → oFunctor).
  Variable (St : R → oFunctor).

  Definition reifier_type (r : R) : Type :=
    forall (op : Op r) {X} `{!Cofe X},
      ((In op ♯ X) * (St r ♯ X) -n> (Out op ♯ X) * (St r ♯ X))%type.

  Variable (Re : forall r, reifier_type r).

  Inductive hvec : nat → Type :=
  | nil : hvec 0
  | cons {n} : R → hvec n → hvec (S n).

  Definition hvec_S_inv {n} (P : hvec (S n) → Type)
    (Hcons : ∀ sR v, P (cons sR v)) v : P v.
  Proof.
    revert P Hcons.
    refine match v with nil => tt
                      | cons sR v => λ P Hcons, Hcons sR v end.
  Defined.

  Global Instance hvec_lookup_total : ∀ m, LookupTotal (fin m) R (hvec m) :=
  fix go m i {struct i} := let _ : ∀ m, LookupTotal _ _ _ := @go in
  match i in fin m return hvec m → R with
  | 0%fin => hvec_S_inv (λ _, R) (λ x _, x)
  | FS j => hvec_S_inv (λ _, R) (λ _ v, v !!! j)
  end.

  (** global signature *)
  Definition glob_Op {n} (rs : hvec n) : Type :=
    { i : fin n & Op (rs !!! i) }.
  Definition glob_In {n} {rs : hvec n} : glob_Op rs → oFunctor :=
    λ iop, @In (rs !!! projT1 iop) (projT2 iop).
  Definition glob_Out {n} {rs : hvec n} : glob_Op rs → oFunctor :=
    λ iop, @Out (rs !!! projT1 iop) (projT2 iop).

  Fixpoint glob_St {n} (rs : hvec n) : oFunctor :=
    match rs with
    | nil => unitO
    | cons r rs => St r * glob_St rs
    end%OF.

  Fixpoint glob_St_rest {n} (i : fin n) : hvec n → oFunctor :=
    match i in fin n return hvec n → oFunctor with
    | 0%fin => hvec_S_inv (λ _, oFunctor)
                 (λ _ rs, glob_St rs)
    | FS j => hvec_S_inv (λ _, oFunctor)
                 (λ r rs, St r * glob_St_rest j rs)%OF
    end.

  Lemma glob_St_decomp' {m} (i : fin m) (rs : hvec m) {X} `{!Cofe X} :
    ofe_iso (glob_St rs ♯ X) ((St (rs !!! i) ♯ X) * (glob_St_rest i rs ♯ X))%type.
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
  Qed.
  Definition glob_St_decomp {m} (i : fin m) {rs : hvec m} {X} `{!Cofe X} :
    (glob_St rs ♯ X) -n> ((St (rs !!! i) ♯ X) * (glob_St_rest i rs ♯ X))%type
    := ofe_iso_1 (glob_St_decomp' i rs).
  Program Definition glob_St_recomp {m} {i : fin m} {rs : hvec m} {X} `{!Cofe X} :
    (glob_St_rest i rs ♯ X) -n> (St (rs !!! i) ♯ X) -n> (glob_St rs ♯ X)
    := λne rest st, ofe_iso_2 (glob_St_decomp' i rs) (st, rest).
  Solve All Obligations with solve_proper_please.

  Lemma glob_St_decomp_recomp {m} (i : fin m) {rs : hvec m} {X} `{!Cofe X}
    (σ : St (rs !!! i) ♯ X) rest :
    glob_St_decomp i (glob_St_recomp rest σ) ≡ (σ, rest).
  Proof. rewrite ofe_iso_12. reflexivity. Qed.

  Definition glob_Re {n} {rs : hvec n} (op : glob_Op rs) {X} `{!Cofe X} :
    (glob_In op ♯ X) * (glob_St rs ♯ X) → (glob_Out op ♯ X) * (glob_St rs ♯ X)
    :=  λ xst,
      let  i := projT1 op in
      let op' := projT2 op in
      let x := xst.1 in
      let st := xst.2 in
      let fs := glob_St_decomp i st in
      let σ := fs.1 in
      let rest := fs.2 in
      let rx := Re (rs !!! i) op' _ _ (x, σ) in
      (rx.1, glob_St_recomp rest rx.2).

  Record in_hvec {n} (r : R) (rs : hvec n) : Type :=
    { idx : fin n;
      opF : Op r → Op (rs !!! idx);
      inF {X} `{!Cofe X} (op : Op r) :
        ofe_iso (In op ♯ X) (In (opF op) ♯ X);
      outF {X} `{!Cofe X} (op : Op r) :
        ofe_iso (Out op ♯ X) (Out (opF op) ♯ X);
      stF  {X} `{!Cofe X} :
        ofe_iso (St r ♯ X) (St (rs !!! idx) ♯ X);
      reF {X} `{!Cofe X} (op : Op r) (x : In op ♯ X)
          (y : Out op ♯ X) (s1 s2 : St r ♯ X) :
        Re r op X _ (x, s1) ≡ (y, s2) →
          Re (rs !!! idx) (opF op) X _ (ofe_iso_1 (inF op) x, ofe_iso_1 stF s1) ≡
            (ofe_iso_1 (outF op) y, ofe_iso_1 stF s2)
    }.
  Arguments idx {_ _ _} _.

  Definition in_hvec_op {n} {r : R} {rs : hvec n} (rin : in_hvec r rs)
    (op : Op r) : glob_Op rs.
  Proof.
    refine (existT (idx rin) _).
    apply (opF _ _ rin op).
  Defined.
  Definition in_hvec_in {n} {r : R} {rs : hvec n} (rin : in_hvec r rs)
                        {X} `{Cofe X} (op : Op r)
    (x : In op ♯ X) : glob_In (in_hvec_op rin op) ♯ X.
  Proof.
    unfold glob_In.
    unfold in_hvec_op; simpl.
    apply (ofe_iso_1 (inF _ _ _ _) x).
  Defined.
  Definition in_hvec_st {n} {r : R} {rs : hvec n} (rin : in_hvec r rs)
                        {X} `{Cofe X} (op : Op r)
    (x : St r ♯ X) : St (rs !!! idx rin) ♯ X.
  Proof.
    apply (ofe_iso_1 (stF _ _ _) x).
  Defined.
  Definition in_hvec_out {n} {r : R} {rs : hvec n} (rout : in_hvec r rs)
                        {X} `{Cofe X} (op : Op r)
    (x : Out op ♯ X) : glob_Out (in_hvec_op rout op) ♯ X.
  Proof.
    unfold glob_Out.
    unfold in_hvec_op; simpl.
    apply (ofe_iso_1 (outF _ _ _ _) x).
  Defined.

  Lemma glob_Re_idx {n} (r : R) (rs : hvec n) (rin : in_hvec r rs)
    {X} `{!Cofe X} (i : fin n) (op : Op (rs !!! i))
    (x : In op ♯ X) (σ : St (rs !!! i) ♯ X) (rest : glob_St_rest i rs ♯ X) :
    glob_Re (existT i op) (x,glob_St_recomp rest σ) ≡
      prodO_map idfun (glob_St_recomp rest) $ Re (rs !!! i) op X _ (x,σ).
  Proof.
    Opaque glob_St_recomp.
    unfold glob_Re. simpl.
    trans (((Re (rs !!! i) op X _ (x, σ)).1, glob_St_recomp rest (Re (rs !!! i) op X _ (x, σ)).2)).
    { repeat f_equiv; rewrite glob_St_decomp_recomp//. }
    destruct (Re (rs !!! i) op X _ (x, σ)) as [y σ'].
    simpl. reflexivity.
  Qed.

  Lemma in_hvec_re {n} (r : R) (rs : hvec n) (rin : in_hvec r rs)
                   {X} `{!Cofe X}
                   (op : Op r) (x : In op ♯ X) (σ : St r ♯ X)
                   (y : Out op ♯ X) (σ' : St r ♯ X)
                   (rest : glob_St_rest (idx rin) rs ♯ X)
    : Re r op X _ (x,σ) ≡ (y, σ') →
      glob_Re (in_hvec_op rin op)
        (in_hvec_in rin _ x,glob_St_recomp rest (in_hvec_st rin op σ))
        ≡ (in_hvec_out rin _ y, glob_St_recomp rest (in_hvec_st rin op σ')).
  Proof.
    intros Hre.
    apply (reF r rs rin) in Hre.
    unfold in_hvec_op.
    rewrite glob_Re_idx//.
    rewrite Hre. simpl. reflexivity.
  Qed.

End abstract_reseeee.


Section reify.
  Definition reify_eff (E : opsInterp) (stateF : oFunctor) :=
    ∀ (op : opid E) (X : ofe) `{Cofe X},
      ((Ins (E op) ♯ X) * (stateF ♯ X) -n> optionO ((Outs (E op) ♯ X) * (stateF ♯ X)))%type.

  Record sReifier :=
    { sReifier_ops : opsInterp;
      sReifier_state : oFunctor;
      sReifier_re : reify_eff sReifier_ops sReifier_state;
      sReifier_inhab :: Inhabited (sReifier_state ♯ unitO);
      sReifier_cofe X (HX : Cofe X) :: Cofe (sReifier_state ♯ X);
    }.
  Set Printing Universes.
  About list. About Vector.t.
  Coercion  sReifier_re : sReifier >-> Funclass.

  Inductive gReifiers : nat → Type :=
  | gReifiers_nil : gReifiers 0
  | gReifiers_cons {n} : sReifier → gReifiers n → gReifiers (S n)
  .

  Fixpoint gReifiers_state {n} (rs : gReifiers n) : oFunctor :=
    match rs with
    | gReifiers_nil => unitO
    | gReifiers_cons sR rs => sReifier_state sR * (gReifiers_state rs)
    end.

  Fixpoint gReifiers_ops {n} (rs : gReifiers n) : opsInterp :=
    match rs with
    | gReifiers_nil => opsInterp.nil
    | gReifiers_cons sR rs => opsInterp.app (sReifier_ops sR) (gReifiers_ops rs)
    end.

  Definition grs_S_inv {n} (P : gReifiers (S n) → Type)
    (Hcons : ∀ sR v, P (gReifiers_cons sR v)) v : P v.
  Proof.
    revert P Hcons.
    refine match v with gReifiers_nil => tt
                      | gReifiers_cons sR v => λ P Hcons, Hcons sR v end.
  Defined.

  Global Instance gReifiers_lookup_total : ∀ m, LookupTotal (fin m) sReifier (gReifiers m) :=
  fix go m i {struct i} := let _ : ∀ m, LookupTotal _ _ _ := @go in
  match i in fin m return gReifiers m → sReifier with
  | 0%fin => grs_S_inv (λ _, sReifier) (λ x _, x)
  | FS j => grs_S_inv (λ _, sReifier) (λ _ v, v !!! j)
  end.

  Fixpoint gReifiers_state_rest {m} (i : fin m) : gReifiers m → oFunctor :=
    match i in fin m return gReifiers m → oFunctor with
    | 0%fin => grs_S_inv (λ _, oFunctor)
                 (λ sR rs, gReifiers_state rs)
    | FS j => grs_S_inv (λ _, oFunctor)
                 (λ sR rs, sReifier_state sR * gReifiers_state_rest j rs)%OF
    end.

  Lemma rs_state_decomp {m} (i : fin m) (rs : gReifiers m) {X} `{!Cofe X} :
    ofe_iso ((sReifier_state (rs !!! i) ♯ X) * (gReifiers_state_rest i rs ♯ X))%type
            (gReifiers_state rs ♯ X).
  Proof.
    revert i. induction rs as [|? [F stateF re ? ?] rs]=>i.
    { inversion i. }
    inv_fin i; simpl.
    { apply iso_ofe_refl. }
    intros i.
    specialize (IHrs i).
    unshelve esplit.
    - simple refine (λne sxr, let r' := ofe_iso_1 IHrs (sxr.1,sxr.2.2) in
                              (sxr.2.1, r')).
      solve_proper.
    - simple refine (λne xr, let sr := ofe_iso_2 IHrs (xr.2) in
                             (sr.1,(xr.1,sr.2))).
      solve_proper.
    - intros (x & r). simpl. f_equiv.
      rewrite -surjective_pairing. apply ofe_iso_12.
    - intros (s & x & r). simpl. repeat f_equiv; rewrite ofe_iso_21//.
  Qed.

  #[export] Instance reifiers_state_cofe {n} (rs : gReifiers n) X `{!Cofe X} :
    Cofe (gReifiers_state rs ♯ X).
  Proof.
    induction rs; simpl; first apply _.    destruct s. apply _.
  Qed.
  #[export] Instance reifiers_state_inhab {n} (rs : gReifiers n) :
    Inhabited (gReifiers_state rs ♯ unitO).
  Proof.
    induction rs; simpl; first apply _.
    destruct s. apply _.
  Qed.

  Definition reifiers_op_idx' {n} (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) :
    { i : fin n & opid (sReifier_ops (rs !!! i)) }.
  Proof.
    induction rs as [|? sR rs].
    { apply Empty_set_rect. exact op. }
    simpl in op.
    destruct op as [op|op]; simpl.
    - refine (existT 0%fin op).
    - pose (i := projT1 (IHrs op)).
      exact (existT (FS i) (projT2 (IHrs op))).
  Defined.
  Definition reifiers_op_idx {n} (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) : fin n
    := projT1 $ reifiers_op_idx' rs op.
  Definition reifiers_op_conv {n} (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) : opid (sReifier_ops (rs !!! reifiers_op_idx rs op))
    := projT2 $ reifiers_op_idx' rs op.
  Lemma reifiers_op_idx_0 {n} (sR : sReifier) (rs : gReifiers n)
    (op : opid (sReifier_ops sR)) :
    reifiers_op_idx (gReifiers_cons sR rs) (inl op) = 0%fin.
  Proof. reflexivity. Qed.
  Lemma reifiers_op_idx_S {n} (sR : sReifier) (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) :
    reifiers_op_idx (gReifiers_cons sR rs) (inr op) = FS $ reifiers_op_idx rs op.
  Proof. reflexivity. Qed.

  (* those are just identities? *)
  Definition reifiers_op_conv_ins {n} (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) {X} `{!Cofe X}:
    ofe_iso (Ins (gReifiers_ops rs op) ♯ X)
      (Ins (sReifier_ops (rs !!! (reifiers_op_idx rs op)) (reifiers_op_conv rs op)) ♯ X).
  Proof.
    induction rs as [|? [F stateF re ? ?] rs].
    { apply Empty_set_rect. exact op. }
    simpl in op.
    destruct op as [op|op].
    - unfold reifiers_op_conv. simpl.
      apply iso_ofe_refl.
    - simpl. unfold reifiers_op_conv.
      apply IHrs.
  Defined.
  Definition reifiers_op_conv_outs {n} (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) {X} `{!Cofe X}:
    ofe_iso (Outs (gReifiers_ops rs op) ♯ X)
      (Outs (sReifier_ops (rs !!! (reifiers_op_idx rs op)) (reifiers_op_conv rs op)) ♯ X).
  Proof.
    induction rs as [|? [F stateF re ? ?] rs].
    { apply Empty_set_rect. exact op. }
    simpl in op.
    destruct op as [op|op].
    - unfold reifiers_op_conv. simpl.
      apply iso_ofe_refl.
    - simpl. unfold reifiers_op_conv.
      apply IHrs.
  Defined.

  Program Definition reifiers_op_conv_state {n} {i : fin n} {rs : gReifiers n}
   {X} `{!Cofe X} :
    (rs_state_rest i rs ♯ X) -n>
    (sReifier_state (rs !!! i) ♯ X) -n>
      gReifiers_state rs ♯ X :=
    λne rest σ1,  ofe_iso_1 (rs_state_decomp i rs) (σ1,rest).
  Solve All Obligations with solve_proper_please.

  Program Definition reifiers_op_conv_state' {n} (i : fin n) {rs : gReifiers n}
    {X} `{!Cofe X} :
    gReifiers_state rs ♯ X -n>
      (prodO (sReifier_state (rs !!! i) ♯ X) (rs_state_rest i rs ♯ X))
    := ofe_iso_2 (rs_state_decomp i rs).

  Definition reifiers_re_idx {n} (i : fin n) (rs : gReifiers n)
    (op : opid (sReifier_ops (rs !!! i))) (X : ofe) `{Cofe X} :
    ((Ins (sReifier_ops (rs !!! i) op) ♯ X) * (gReifiers_state rs ♯ X)
     → optionO ((Outs (sReifier_ops (rs !!! i) op) ♯ X) * (gReifiers_state rs ♯ X)))%type.
  Proof.
    intros [inp s].
    set (σ := fst (reifiers_op_conv_state' i s)).
    set (rest := snd (reifiers_op_conv_state' i s)).
    simple refine (optionO_map (prodO_map idfun (reifiers_op_conv_state rest)) (sReifier_re (rs !!! i) op X _ (inp, σ))).
  Defined.

  #[global] Instance reifiers_re_idx_ne  {n} (i : fin n) (rs : gReifiers n)
    (op : opid (sReifier_ops (rs !!! i))) (X : ofe) `{Cofe X} :
    NonExpansive (reifiers_re_idx i rs op X).
  Proof.
    intros m [i1 s1] [i2 s2] [Hi Hs].
    unfold reifiers_re_idx. repeat f_equiv; eauto.
  Qed.

  (* Definition reifiers_re {n} (rs : gReifiers n) *)
  (*   (op : opid (gReifiers_ops rs)) (X : ofe) `{Cofe X} : *)
  (*   ((Ins (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X) *)
  (*    → optionO ((Outs (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X)))%type. *)
  (* Proof. *)
  (*   intros xs. *)
  (*   refine *)
  (*     (optionO_map (prodO_map (ofe_iso_2 (reifiers_op_conv_outs rs op)) idfun) $ reifiers_re_idx (reifiers_op_idx rs op) rs (reifiers_op_conv rs op) X *)
  (*        (ofe_iso_1 (reifiers_op_conv_ins rs op) xs.1, xs.2)). *)
  (* Defined. *)
  Definition reifiers_re {n} (rs : gReifiers n)
    (op : opid (gReifiers_ops rs)) (X : ofe) `{Cofe X} :
    ((Ins (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X)
     → optionO ((Outs (gReifiers_ops rs op) ♯ X) * (gReifiers_state rs ♯ X)))%type.
  Proof.
    induction rs as [|? sR rs].
    { inversion op. }
    simpl in op.
    destruct op as [op|op]; cbn-[oFunctor_apply].
    - intros [x [s1 s2]].
      apply (option_map (prod_map idfun (λ s1', (s1',s2))) (sReifier_re sR op X _ (x,s1))).
    - intros [x [s1 s2]].
      apply
        (option_map (prod_map idfun (λ s2', (s1,s2'))) (IHrs _ (x,s2))).
  Defined.


  #[global] Instance reifiers_re_ne {n} (rs : gReifiers n)
       (op : opid (gReifiers_ops rs)) (X : ofe) `{Cofe X} :
    NonExpansive (reifiers_re rs op X).
  Proof.
    (* unfold reifiers_re. solve_proper_please. *)
  Admitted.
  #[global] Instance reifiers_re_proper  {n} (rs : gReifiers n)
       (op : opid (gReifiers_ops rs)) (X : ofe) `{Cofe X} :
    Proper ((≡) ==> (≡)) (reifiers_re rs op X).
  Proof. apply ne_proper. apply _. Qed.

  (* Class inReifier {n} (sR : sReifier) (rs : gReifiers n) := *)
  (*   { inR_idx : fin n; *)
  (*     inR_lookup : rs !!! inR_idx = sR *)
  (*   }. *)
  Class inReifier {n} (sR : sReifier) (rs : gReifiers n) :=
    { inR_idx : fin n;
      inR_sub :: subEff (sReifier_ops sR) (sReifier_ops (rs !!! inR_idx));
      inR_state X `{!Cofe X} :
         ofe_iso (sReifier_state sR ♯ X)
                 (sReifier_state (rs !!! inR_idx) ♯ X);
      inR_reify X `{!Cofe X} (op : opid (sReifier_ops sR))
          (x : Ins (sReifier_ops sR op) ♯ X)
          (s : sReifier_state sR ♯ X) :
      let x' : Ins (sReifier_ops (rs !!! inR_idx) (subEff_opid op)) ♯ X
        := subEff_conv_ins x in
      let s' : sReifier_state (rs !!! inR_idx) ♯ X
        := ofe_iso_1 (inR_state X) s in
         sReifier_re sR op X _ (x , s) ≡
         optionO_map (prodO_map subEff_conv_outs2 (ofe_iso_2 (inR_state X))) $
           sReifier_re (rs !!! inR_idx) (subEff_opid op) X _ (x', s')
    }.
  Definition inReifier_st_conv {n} {sR} {rs : gReifiers n} `{!inReifier sR rs}
    {X} `{!Cofe X}:
    sReifier_state sR ♯ X -n> sReifier_state (rs !!! inR_idx) ♯ X
    := ofe_iso_1 (inR_state X).
  Definition inReifier_st_conv2 {n} {sR} {rs : gReifiers n} `{!inReifier sR rs}
    {X} `{!Cofe X}:
    sReifier_state (rs !!! inR_idx) ♯ X -n> sReifier_state sR ♯ X
    := ofe_iso_2 (inR_state X).

  (* Program Definition sRs_transport {A B : sReifier} (H : A = B) *)
  (*   {X} `{!Cofe X} : *)
  (*   ofe_iso (sReifier_state A ♯ X) (sReifier_state B ♯ X) *)
  (*   := eq_rect A (λ B, ofe_iso (sReifier_state B ♯ X) (sReifier_state B ♯ X)) *)
  (*        iso_ofe_refl B H. *)
  (* Next Obligation. solve_proper. Qed. *)

  (* Definition sReq_opid {A B : sReifier} (H : A = B) : *)
  (*   opid (sReifier_ops A) = opid (sReifier_ops B). *)
  (* Proof. *)
  (*   induction H. reflexivity. *)
  (* Defined. *)
  (* Definition sRop_transport {A B : sReifier} (H : A = B) : *)
  (*   opid (sReifier_ops A) → opid (sReifier_ops B). *)
  (* Proof. *)
  (*   induction H. exact id. *)
  (* Defined. *)

  (* Definition inR_opid {n} {sR} (rs : gReifiers n) {i : fin n} *)
  (*   (Hi : rs !!! i = sR): *)
  (*   opid (sReifier_ops sR) → opid (gReifiers_ops rs). *)
  (* Proof. *)
  (*   induction rs as [|? sR' rs]. *)
  (*   { inversion i. } *)
  (*   inv_fin i. *)
  (*   { simpl. intros Hsr. *)
  (*     refine (inl ∘ sRop_transport (eq_sym Hsr)). } *)
  (*   intros i. simpl. intros Hi. *)
  (*   refine (inr ∘ IHrs i Hi). *)
  (* Defined. *)

  (* Definition subEff_transp {sR sR'} (H : sR = sR') : *)
  (*   subEff (sReifier_ops sR) (sReifier_ops sR'). *)
  (* Proof. *)
  (*   refine {| subEff_opid := sRop_transport H |}. *)
  (*   - intros. *)
  (*     assert ((sReifier_ops sR op) = (sReifier_ops sR' (sRop_transport H op))). *)
  (*     { *)
  (*       rewrite sReq_opid. *)
  (*     intros op X HX. *)
  #[global] Instance inR_subEff' {n} (i : fin n) (rs : gReifiers n) :
    subEff (sReifier_ops (rs !!! i)) (gReifiers_ops rs).
  Proof.
    induction rs as [|? sR' rs].
    { inversion i. }
    inv_fin i.
    { simpl. apply _. }
    intros i. simpl.
    apply subEff_app_r.
    apply IHrs.
  Defined.

  Definition subEff_comp E1 E2 E3 :
    subEff E1 E2 → subEff E2 E3 → subEff E1 E3.
  Proof.
    intros H1 H2.
    simple refine
             {| subEff_opid (op : opid E1) := subEff_opid (subEff_opid op) |}.
    - intros.
      eapply iso_ofe_trans.
      + apply subEff_ins.
      + apply subEff_ins.
    - intros.
      eapply iso_ofe_trans.
      + apply subEff_outs.
      + apply subEff_outs.
  Defined.

  #[global] Instance inR_subEff {n} sR (rs : gReifiers n) :
    inReifier sR rs → subEff (sReifier_ops sR) (gReifiers_ops rs).
  Proof.
    intros HR.
    eapply subEff_comp.
    - apply HR.
    - apply inR_subEff'.
  Defined.

  Global Instance optionO_map_proper A B f :
    Proper ((≡) ==> (≡)) (@optionO_map A B f).
  Proof. apply ne_proper. apply _. Qed.


  (* XXX: see why sReifier_re does not work as a good coercion here *)
  Lemma inR_subreify {n} sR (rs : gReifiers n)
   {inR0 : inReifier sR rs}
    {X} `{!Cofe X}
    (σ : sReifier_state sR ♯ X)
    (rest : rs_state_rest inR_idx rs ♯ X)
    (op : opid (sReifier_ops sR))
    (i : Ins (sReifier_ops sR op) ♯ X)
    :
    let σ1 := inReifier_st_conv σ in
    let fs1 := reifiers_op_conv_state rest σ1 in
    reifiers_re rs (subEff_opid op) X (ofe_iso_1 (subEff_ins op) i, fs1) ≡
     optionO_map (prodO_map subEff_conv_outs (reifiers_op_conv_state rest ◎ inReifier_st_conv))
      (sReifier_re sR op X _ (i, σ)).
  Proof.
    intros σ1.
    set (i' := subEff_conv_ins i).
    intros fs1.
    assert (sReifier_re sR op X _ (i,σ) ≡
       optionO_map (prodO_map subEff_conv_outs2 inReifier_st_conv2)
       (sReifier_re (rs !!! inR_idx) (subEff_opid op) X _ (i', σ1))) as Heq.
    { apply inR_reify. }
    pose (op1 :=  (@subEff_opid (sReifier_ops sR) (sReifier_ops (rs !!! @inR_idx n sR rs inR0))) inR_sub op).
    fold op1 in Heq.
    pose  (op' := @subEff_opid _ (@gReifiers_ops n rs)
                    (@inR_subEff' n _ rs) op1).
    change (@subEff_opid (sReifier_ops sR) (@gReifiers_ops n rs) (@inR_subEff n sR rs inR0) op) with op'.
    induction rs as [|? sR' rs].
    { pose (j:= inR_idx). inversion j. }
    simpl in op'. 
    remember op' as op2.
    Set Printing All.
    Etrans. 2:{
            apply optionO_map_proper.
            symmetry. apply Heq. }
          unfold reifiers_re. simpl fst. simpl snd.
    pose (op1 :=  (@subEff_opid (sReifier_ops sR) (sReifier_ops (rs !!! @inR_idx n sR rs inR0))) inR_sub op).
    fold op1.
    pose  (op' := @subEff_opid _ (@gReifiers_ops n rs)
                    (@inR_subEff' n _ rs) op1).
Set Printing Implicit.
    fold op'.
    induction rs as [|? sR' rs].
    { pose (j:= inR_idx). inversion j. }
    simpl in op'.
    destruct op' as [op'|op'].
    simpl reifiers_op_idx.
    simpl.
    unfold reifiers_re. simpl.
    
    set ().
    set (| 
    Check .
    
    : let σ1 := ofe_iso_2 (sRs_transport inR_lookup) σ in
      let fs1 := reifiers_op_conv_state rest σ1 in
   reifiers_re rs (subEff_opid op) X (ofe_iso_1 (subEff_ins op) i, fs1) ≡
   optionO_map (prodO_map (ofe_iso_1 (subEff_outs op)) (reifiers_op_conv_state rest ◎ ofe_iso_2 (sRs_transport inR_lookup)))
     (sReifier_re sR op X _ (i, σ)).
  Proof.
    revert op i σ rest.
    induction rs as [|? sR' rs]=>op i σ rest.
    { destruct inR0.
      inversion inR_idx0. }
    pose (HH := inR_subEff _ _ inR0).
    destruct inR0.
    inv_fin inR_idx0.
    { intros Heq rest HH.
      simpl in Heq.
      unfold reifiers_re.
      Set Printing Implicit.
      simpl subEff_opid.
      assert (reifiers_op_idx rs op)
      simpl.
      generalize (@subEff_opid (sReifier_ops sR) (@gReifiers_ops (S n) (@gReifiers_cons n sR1 rs))
       (@inR_subEff (S n) sR (@gReifiers_cons n sR1 rs)
          {| inR_idx := 0%fin; inR_lookup := Heq |}) op).
      generalize (subEff_opid op : opid (gReifiers_ops (gReifiers_cons sR1 rs))).
      simpl reifiers_re.
      destruct  as [op1|op1].
    Set Printing All.

      simpl.
Eval simpl in . 
      simpl reifiers_re.
      unfold inR_conv_state.
      simpl inR_conv_state.
      simpl.

      
[F stateF re ? ?]
    s
    set fs1 := inR_conv_state rest σ.
    refine (reifiers_re rs (subEff_opid op) X (ofe_iso_1 (subEff_ins op) i,fs1) = _).
    refine (optionO_map _ (sReifier_re sR op X _ (i,σ))).
    refine (prodO_map (ofe_iso_1 (subEff_outs op)) _).
    apply (inR_conv_state rest).
    Show Proof.
    refine (_ ◎ _); last first.
    + apply (sRs_transport (eq_sym inR_lookup)).
    + refine (λne σ2, ofe_iso_1 (rs_state_decomp inR_idx rs) (σ2, rest)).
      solve_proper.
        Show Proof.
      subR_reify (op : opid F) X `{Cofe X}
        (i : Ins (F op) ♯ X) (s : stateF ♯ X) (s_rest : rest ♯ X) :
        let i' := subEff_conv_ins i in
        let s' := subState_conv_state s_rest s in
        reifiers_re rs (subEff_opid op) X (i',s') ≡
          optionO_map (prodO_map subEff_conv_outs (subState_conv_state s_rest))
                      (re op X _ (i,s))

               

  Context {n : nat} (rs : gReifiers n).
  Notation F := (gReifiers_ops rs).
  Notation stateF := (gReifiers_state rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).

  Notation stateM := ((stateF ♯ IT -n> (stateF ♯ IT) * IT))%type.
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
    - simple refine (let ns := reifiers_re rs op _ (oFunctor_map _ (inlO,fstO) i, s) in _).
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
      (oFunctor_map (Ins (F op)) (inlO, fstO)
                    (oFunctor_map (Ins (F op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
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
                   (oFunctor_map (Outs (F op)) (prod_in idfun reify, sumO_rec idfun unreify)
                      (oFunctor_map (Outs (F op)) (fstO, inlO) ns.1)))))))
             (σ, Err RuntimeErr) (Some (o,σ'))).
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
    pose (r := (reifiers_re rs op _
      (oFunctor_map (Ins (F op)) (inlO, fstO)
                    (oFunctor_map (Ins (F op)) (sumO_rec idfun unreify, prod_in idfun reify) i), σ))).
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
    reify (Vis i op k) σ ≡ (σ', β) → (∃ β', β ≡ Tick β') ∨ (β ≡ Err RuntimeErr).
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
Arguments reify {n} rs.



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

