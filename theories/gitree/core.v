From iris.prelude Require Import options.
From iris.algebra Require cofe_solver.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.
From gitrees Require Import prelude.

(*XXX*) Opaque laterO_map.

Local Open Scope type.


(** * Parametrized interpretations for operations *)

(* signatures for the operations *)
Structure opInterp := OpInterp {
  Ins : oFunctor;
  Outs : oFunctor;
  opInterp_ins_contractive : oFunctorContractive Ins;
  opInterp_outs_contractive : oFunctorContractive Outs;
  opInterp_ins_cofe T {H:Cofe T} : Cofe (Ins ♯ T);
  opInterp_outs_cofe T {H:Cofe T} : Cofe (Outs ♯ T);
}.

Global Arguments OpInterp _ _ {_ _ _ _}.
#[export] Existing Instance   opInterp_ins_contractive.
#[export] Existing Instance   opInterp_outs_contractive.
#[export] Existing Instance   opInterp_ins_cofe.
#[export] Existing Instance   opInterp_outs_cofe.
Add Printing Constructor opInterp.

Record opsInterp : Type := OpsInterp {
    opid : Type;
    opid_eqdec :: EqDecision opid;
    opsInterp_lookup :> opid → opInterp;
}.

Module opsInterp.
  Program Definition nil : opsInterp := OpsInterp Empty_set _ (Empty_set_rect _).

  Program Definition singleton (F : opInterp) : opsInterp :=
    OpsInterp unit _ (λ _, F).

  Program Definition app (E1 E2 : opsInterp) : opsInterp :=
    OpsInterp (opid E1 + opid E2) _ (sum_rect (λ _, opInterp) E1 E2).
End opsInterp.

Coercion opsInterp.singleton : opInterp >-> opsInterp.
Notation "@[ ]" := opsInterp.nil (format "@[ ]").
Notation "@[ Σ1 ; .. ; Σn ]" :=
  (opsInterp.app Σ1 .. (opsInterp.app Σn opsInterp.nil) ..).

Class subEff (F E : opsInterp) := {
    subEff_opid : opid F → opid E;
    subEff_ins {op: opid F} {X} `{Cofe X} :
      Ins (F op) ♯ X ≃ Ins (E (subEff_opid op)) ♯ X;
    subEff_outs {op: opid F} {X} `{Cofe X} :
      Outs (F op) ♯ X ≃ Outs (E (subEff_opid op)) ♯ X;
  }.
Definition subEff_id F : subEff F F :=
  {| subEff_opid := id;
    subEff_ins op X _ := iso_ofe_refl;
    subEff_outs op X _ := iso_ofe_refl;
  |}.
Definition subEff_app_l F E1 E2 `{!subEff F E1} : subEff F (opsInterp.app E1 E2).
Proof.
  simple refine
           {| subEff_opid (op : opid F) :=
               inl (subEff_opid op) : opid (opsInterp.app E1 E2) |}.
  - simpl. intros. apply subEff_ins.
  - simpl. intros. apply subEff_outs.
Defined.
Definition subEff_app_r F E1 E2 `{!subEff F E2} : subEff F (opsInterp.app E1 E2).
Proof.
  simple refine
           {| subEff_opid (op : opid F) :=
               inr (subEff_opid op) : opid (opsInterp.app E1 E2) |}.
  - simpl. intros. apply subEff_ins.
  - simpl. intros. apply subEff_outs.
Defined.

Inductive error :=
  RuntimeErr
| OtherError
.
Canonical Structure errorO := leibnizO error.

(** * Recursive domain equation *)
Module IT_pre.
Definition ITOF (Σ : opsInterp) (A : ofe) : oFunctor :=
  ( A           (* basic values *)
  + ▶ (∙ -n> ∙) (* function space *)
  + errorO  (* explicit error state *)
  + ▶ ∙  (* silent step *)
  + { op : opid Σ & (Ins (Σ op)) * ((Outs (Σ op)) -n> ▶ ∙ ) }
  ).

#[export] Instance ITOF_contractive Σ A : oFunctorContractive (ITOF Σ A).
Proof. apply _. Qed.

#[export] Instance ITOF_inhabited Σ A : Inhabited (oFunctor_apply (ITOF Σ A) unitO).
Proof.
  refine (populate _).
  refine (inl (inr _)). refine (Next tt).
Defined.

#[export]  Instance ITOF_cofe Σ A `{!Cofe A} T `{!Cofe T}:
  Cofe (oFunctor_apply (ITOF Σ A) T).
Proof. apply _. Defined.
End IT_pre.

Module Export ITF_solution.
  Import IT_pre.
  Import cofe_solver.
  Definition IT_result Σ A `{!Cofe A}:
    solution (ITOF Σ A) := solver.result (ITOF Σ A).

  Definition IT Σ A `{!Cofe A} : ofe := (IT_result Σ A).
  Global Instance IT_cofe Σ A `{!Cofe A} : Cofe (IT Σ A) := _.


  Definition IT_unfold {Σ A} `{!Cofe A} :
    IT Σ A -n> sumO (sumO (sumO (sumO A (laterO (IT Σ A -n> IT Σ A)))
                                         errorO)
                                          (laterO (IT Σ A)))
                (sigTO (λ op : opid Σ, prodO (Ins (Σ op) ♯ (IT Σ A))
                                             ((Outs (Σ op) ♯ (IT Σ A)) -n> laterO (IT Σ A))))
    := ofe_iso_2 (IT_result Σ A).

  Definition IT_fold {Σ A} `{!Cofe A} :
    sumO (sumO (sumO (sumO A (laterO (IT Σ A -n> IT Σ A)))
                                         errorO)
                                          (laterO (IT Σ A)))
                (sigTO (λ op : opid Σ, prodO (Ins (Σ op) ♯ (IT Σ A))
                                             ((Outs (Σ op) ♯ (IT Σ A)) -n> laterO (IT Σ A))))
         -n> IT Σ A
    := ofe_iso_1 (IT_result Σ A).

  Lemma IT_fold_unfold {Σ A} `{!Cofe A} (T : IT Σ A) : IT_fold (IT_unfold T) ≡ T.
  Proof. apply ofe_iso_12. Qed.
  Lemma IT_unfold_fold {Σ : opsInterp} {A} `{!Cofe A} T' : IT_unfold (Σ:=Σ) (A:=A) (IT_fold T') ≡ T'.
  Proof. apply ofe_iso_21. Qed.
End ITF_solution.


(** * Smart constructors *)
Section smart.
  Context {E : opsInterp} {A : ofe} `{!Cofe A}.
  Local Notation IT := (IT E A).

  Definition Ret : A -n> IT.
  Proof.
    refine (IT_fold ◎ inlO ◎ inlO ◎ inlO ◎ inlO).
  Defined.

  Definition Err : errorO -n> IT.
  Proof.
    refine (IT_fold ◎ inlO ◎ inlO ◎ inrO).
  Defined.

  Definition Tau : laterO IT -n> IT.
  Proof.
    refine (IT_fold ◎ inlO ◎ inrO).
  Defined.

  Definition Fun : laterO (IT -n> IT) -n> IT.
  Proof.
    refine (IT_fold ◎ inlO ◎ inlO ◎ inlO ◎ inrO).
  Defined.

  Definition Vis (op : opid E) (ins : oFunctor_apply (Ins (E op)) IT)
             (k : oFunctor_apply (Outs (E op)) IT -n> laterO IT) : IT.
  Proof.
    refine (IT_fold (inr _)).
    refine (existT op (ins, k)).
  Defined.

  Global Instance Vis_ne {op : opid E} n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) (Vis op).
  Proof.
    rewrite /Vis.
    intros i1 i2 Hi k1 k2 Hk.
    f_equiv. f_equiv.
    eapply existT_ne_2. eapply pair_ne; eauto.
  Qed.
  Global Instance Vis_proper {op : opid E} :
    Proper ((≡) ==> (≡) ==> (≡)) (Vis op).
  Proof.
    rewrite /Vis.
    intros i1 i2 Hi k1 k2 Hk.
    f_equiv. f_equiv.
    eapply existT_proper_2.
    solve_proper.
  Qed.

  Global Instance IT_inhab : Inhabited IT.
  Proof. refine (populate (Err OtherError)). Defined.

  Program Definition pre_Bottom : IT -n> IT :=
    λne T, Tau (Next T).
  Next Obligation. solve_proper. Qed.

  Local Instance pre_Bottom_Contractive : Contractive pre_Bottom.
  Proof. solve_contractive. Qed.

  Definition Bottom : IT := fixpoint pre_Bottom.

  Lemma Bottom_unfold : Bottom ≡ Tau (Next Bottom).
  Proof. apply (fixpoint_unfold pre_Bottom). Qed.

  (** Injectivity of the constructors *)
  Lemma Tau_inj' (α β : laterO IT) {PROP : bi} `{!BiInternalEq PROP} :
    (α ≡ β ⊣⊢ (Tau α ≡ Tau β : PROP))%I.
  Proof.
    iSplit.
    - iIntros "H". iRewrite "H". done.
    - iIntros "H".
      iAssert (internal_eq (IT_unfold (Tau α)) (IT_unfold (Tau β))) with "[H]" as "H".
      { iRewrite "H". done. }
      unfold Tau. simpl.
      rewrite !IT_unfold_fold.
      iPoseProof (sum_equivI with "H") as "H".
      iPoseProof (sum_equivI with "H") as "H".
      done.
  Qed.
  Lemma Ret_inj' (k m : A) {PROP : bi} `{!BiInternalEq PROP} :
    (k ≡ m ⊣⊢ (Ret k ≡ Ret m : PROP))%I.
  Proof.
    iSplit.
    - iIntros "H". iRewrite "H". done.
    - iIntros "H".
      iAssert (internal_eq (IT_unfold (Ret k)) (IT_unfold (Ret m))) with "[H]" as "H".
      { iRewrite "H". done. }
      rewrite !IT_unfold_fold. simpl.
      repeat iPoseProof (sum_equivI with "H") as "H".
      done.
  Qed.
  Lemma Err_inj' (e e' : error) {PROP : bi} `{!BiInternalEq PROP} :
    (e ≡ e' ⊣⊢ (Err e ≡ Err e' : PROP))%I.
  Proof.
    iSplit.
    - iIntros "H". iRewrite "H". done.
    - iIntros "H".
      iAssert (internal_eq (IT_unfold (Err e)) (IT_unfold (Err e'))) with "[H]" as "H".
      { iRewrite "H". done. }
      rewrite !IT_unfold_fold. simpl.
      repeat iPoseProof (sum_equivI with "H") as "H".
      done.
  Qed.
  Lemma Fun_inj' (f g : laterO (IT -n> IT)) {PROP : bi} `{!BiInternalEq PROP} :
    (f ≡ g ⊣⊢ (Fun f ≡ Fun g : PROP))%I.
  Proof.
    iSplit.
    - iIntros "H". iRewrite "H". done.
    - iIntros "H".
      iAssert (internal_eq (IT_unfold (Fun f)) (IT_unfold (Fun g))) with "[H]" as "H".
      { iRewrite "H". done. }
      rewrite !IT_unfold_fold. simpl.
      repeat iPoseProof (sum_equivI with "H") as "H".
      done.
  Qed.

  Lemma Vis_inj_op' op1 op2 i1 i2 k1 k2 {PROP : bi} `{!BiInternalEq PROP} :
    (Vis op1 i1 k1 ≡ Vis op2 i2 k2 ⊢ ⌜op1 = op2⌝ : PROP)%I.
  Proof.
    iIntros "H".
    iAssert (internal_eq (IT_unfold (Vis op1 i1 k1)) (IT_unfold (Vis op2 i2 k2))) with "[H]" as "H".
    { iRewrite "H". done. }
    rewrite !IT_unfold_fold.
    iPoseProof (sum_equivI with "H") as "H".
    iPoseProof (sigT_equivI with "H") as "H".
    iDestruct "H" as (eq) "H".
    done.
  Qed.

  Lemma Vis_inj' op i1 i2 k1 k2  {PROP : bi} `{!BiInternalEq PROP} :
    (Vis op i1 k1 ≡ Vis op i2 k2 ⊢ i1 ≡ i2 ∧ k1 ≡ k2 : PROP)%I.
  Proof.
    iIntros "H".
    iAssert (internal_eq (IT_unfold (Vis op i1 k1)) (IT_unfold (Vis op i2 k2))) with "[H]" as "H".
    { iRewrite "H". done. }
    rewrite !IT_unfold_fold. simpl.
    iPoseProof (sum_equivI with "H") as "H".
    iPoseProof (sigT_equivI with "H") as "H".
    iDestruct "H" as (eq) "H". simpl.
    simpl in eq. assert (eq = eq_refl) as ->.
    { apply eq_pi. apply _. }
    simpl. iPoseProof (prod_equivI with "H") as "[$ $]".
  Qed.

  Lemma IT_ret_tau_ne k α {PROP : bi} `{!BiInternalEq PROP} :
    (Ret k ≡ Tau α ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Ret k) ≡ IT_unfold (Tau α))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold.
    iPoseProof (sum_equivI with "H2") as "H".
    iPoseProof (sum_equivI with "H") as "H".
    done.
  Qed.
  Lemma IT_fun_tau_ne f α {PROP : bi} `{!BiInternalEq PROP} :
    (Fun f ≡ Tau α ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Fun f) ≡ IT_unfold (Tau α))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold. simpl.
    iPoseProof (sum_equivI with "H2") as "H2".
    by iPoseProof (sum_equivI with "H2") as "H2".
  Qed.
  Lemma IT_ret_vis_ne n op i k {PROP : bi} `{!BiInternalEq PROP} :
    (Ret n ≡ Vis op i k ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Ret n) ≡ IT_unfold (Vis op i k))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold.
    iPoseProof (sum_equivI with "H2") as "H".
    done.
  Qed.
  Lemma IT_fun_vis_ne f op i ko {PROP : bi} `{!BiInternalEq PROP} :
    (Fun f ≡ Vis op i ko ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Fun f) ≡ IT_unfold (Vis op i ko))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold. simpl.
    by iPoseProof (sum_equivI with "H2") as "H2".
  Qed.
  Lemma IT_tau_vis_ne α op i k {PROP : bi} `{!BiInternalEq PROP} :
    (Tau α ≡ Vis op i k ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Tau α) ≡ IT_unfold (Vis op i k))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold /=.
    iPoseProof (sum_equivI with "H2") as "H2".
    done.
  Qed.
  Lemma IT_ret_fun_ne k f {PROP : bi} `{!BiInternalEq PROP} :
    (Ret k ≡ Fun f ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Ret k) ≡ IT_unfold (Fun f))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold. simpl.
    by repeat iPoseProof (sum_equivI with "H2") as "H2".
  Qed.
  Lemma IT_tau_err_ne α e {PROP : bi} `{!BiInternalEq PROP} :
    (Tau α ≡ Err e ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Tau α) ≡ IT_unfold (Err e))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold /=.
    by repeat iPoseProof (sum_equivI with "H2") as "H2".
  Qed.
  Lemma IT_ret_err_ne n e {PROP : bi} `{!BiInternalEq PROP} :
    (Ret n ≡ Err e ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Ret n) ≡ IT_unfold (Err e))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold /=.
    by repeat iPoseProof (sum_equivI with "H2") as "H2".
  Qed.
  Lemma IT_fun_err_ne n e {PROP : bi} `{!BiInternalEq PROP} :
    (Fun n ≡ Err e ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Fun n) ≡ IT_unfold (Err e))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold /=.
    by repeat iPoseProof (sum_equivI with "H2") as "H2".
  Qed.
  Lemma IT_vis_err_ne op i k e {PROP : bi} `{!BiInternalEq PROP} :
    (Vis op i k ≡ Err e ⊢ False : PROP)%I.
  Proof.
    iIntros "H1".
    iAssert (IT_unfold (Vis op i k) ≡ IT_unfold (Err e))%I with "[H1]" as "H2".
    { by iRewrite "H1". }
    rewrite !IT_unfold_fold /=.
    by iPoseProof (sum_equivI with "H2") as "H2".
  Qed.

End smart.

(** * The recursion principle *)
Section IT_rec.
  (* We are eliminating [IT E] into [P] *)
  Context {E : opsInterp}.
  Context {A : ofe} `{!Cofe A}.
  Variable (P : ofe).
  Context `{!Cofe P, !Inhabited P}.

  Variable
    (Perr : error → P)
    (Pret : A -n> P)
    (Parr : laterO (sumO (IT E A) P -n> prodO (IT E A) P) -n> P)
    (Ptau : laterO (prodO (IT E A) P) -n> P)
    (Pvis : forall (op : opid E),
        (oFunctor_car (Ins (E op)) (sumO (IT E A) P) (prodO (IT E A) P)) -n>
        ((oFunctor_car (Outs (E op)) (prodO (IT E A) P) (sumO (IT E A) P)) -n> laterO (prodO (IT E A) P)) -n>
                                           P).

  Variable (Punfold :
           P -n> sumO (sumO (sumO (sumO A (laterO (P -n> P)))
                          errorO)
                          (laterO P))
                    (sigTO (λ op : opid E, prodO (oFunctor_apply (Ins (E op)) P) ((oFunctor_apply (Outs (E op)) P) -n> laterO P))%type)).

  (** XXX **) Opaque prod_in.
  (** otherwise it gets unfolded in the proofs of contractiveness *)

  Program Definition Pvis_rec (self : prodO (IT E A -n> P) (P -n> IT E A)) :
    sigTO (λ op : opid E, prodO (oFunctor_apply (Ins (E op)) (IT E A)) (oFunctor_apply (Outs (E op)) (IT E A) -n> laterO (IT E A))) -n> P
      := λne x, let op := projT1 x in
              let inp := fst (projT2 x) in
              let outp := snd (projT2 x) in
              let self1 : IT E A -n> P := fst self in
              let self2 : P -n> IT E A := snd self in
              let s_in := oFunctor_map (Ins (E op)) (sumO_rec idfun self2,prod_in idfun self1) in
              let s_out := oFunctor_map (Outs (E op)) (prod_in idfun self1, sumO_rec idfun self2) in
      Pvis op (s_in inp) (laterO_map (prod_in idfun self1) ◎ outp ◎ s_out).
  Next Obligation.
    intros (self1, self2) n x1 x2 Hx.
    destruct x1 as [R1 [q1 k1]].
    destruct x2 as [R2 [q2 k2]].
    destruct Hx as [Hx1 Hx2].
    simpl in *.
    subst. simpl in *.
    destruct Hx2 as [Hx1 Hx2]. simpl in *.
    solve_proper.
  Qed.
  Instance Pvis_rec_contractive : Contractive Pvis_rec.
  Proof. solve_contractive. Qed.

  Program Definition ITvis_rec (self : prodO (IT E A -n> P) (P -n> IT E A)) :
    sigTO (λ op : opid E, prodO (oFunctor_apply (Ins (E op)) P) (oFunctor_apply (Outs (E op)) P -n> laterO P)) -n> IT E A
      := λne x, let op := projT1 x in
                let inp := fst (projT2 x) in
                let outp := snd (projT2 x) in
                let self1 : IT E A -n> P := fst self in
                let self2 : P -n> IT E A := snd self in
                let s_in := oFunctor_map (Ins (E op)) (self1,self2) in
                let s_out := oFunctor_map (Outs (E op)) (self2,self1) in
      Vis op (s_in inp) (laterO_map self2 ◎ outp ◎ s_out).
  Next Obligation.
    intros (self1, self2) n x1 x2 Hx.
    destruct x1 as [R1 [q1 k1]].
    destruct x2 as [R2 [q2 k2]].
    destruct Hx as [Hx1 Hx2].
    simpl in *.
    subst. simpl in *.
    destruct Hx2 as [Hx1 Hx2]. simpl in *.
    solve_proper.
  Qed.
  Instance ITvis_rec_contractive : Contractive ITvis_rec.
  Proof. solve_contractive. Qed.

  Program Definition IT_rec_pre
          (self : prodO (IT E A -n> P) (P -n> IT E A))
     : prodO (IT E A -n> P) (P -n> IT E A).
  Proof using E P Parr Perr Pret Ptau Punfold Pvis.
    set (self1 := fst self).
    set (self2 := snd self).
    simple refine (_,_).
    { refine (_ ◎ IT_unfold).
      repeat refine (sumO_rec _ _).
      - exact Pret.
      - simple refine (Parr ◎ laterO_map _).
        simple refine (λne f, sumO_rec (prod_in idfun self1 ◎ f) (prod_in idfun self1 ◎ f ◎ self2)).
        repeat intro. repeat f_equiv; eauto.
      - simple refine (λne e, Perr e).
      - simple refine (Ptau ◎ laterO_map _).
        simple refine (λne x, (x, self1 x)).
        solve_proper.
     - apply (Pvis_rec self). }
    { refine (_ ◎ Punfold).
      repeat refine (sumO_rec _ _).
      - refine (OfeMor Ret).
      - simple refine (Fun ◎ laterO_map _).
        simple refine (λne f, self2 ◎ f ◎ self1).
        repeat intro. repeat f_equiv; eauto.
      - refine (λne e, Err e).
      - refine (Tau ◎ laterO_map self2).
      - refine (ITvis_rec self).
    }
  Defined.

  Instance IT_rec_contractive : Contractive IT_rec_pre.
  Proof.
    unfold IT_rec_pre.
    intros n [h1 k1] [h2 k2] Hhk.
    repeat (f_contractive
            || f_equiv || destruct Hhk as [Hh Hk]); eauto.
    { repeat intro. cbn-[sumO_rec]. repeat f_equiv; eauto. }
    { repeat intro. simpl. repeat f_equiv; eauto. }
    { repeat intro. simpl. repeat f_equiv; eauto. }
  Qed.

  Definition IT_rec : prodO (IT E A -n> P) (P -n> IT E A) :=
    let _ := _ : Inhabited P in
    fixpoint IT_rec_pre.
  Transparent prod_in.

  Definition IT_rec1 := fst IT_rec.
  Definition IT_rec2 := snd IT_rec.

  Lemma IT_rec_unfold :
    IT_rec ≡ IT_rec_pre IT_rec.
  Proof. apply (fixpoint_unfold IT_rec_pre). Qed.
  Lemma IT_rec1_unfold t :
    IT_rec1 t ≡ (IT_rec_pre IT_rec).1 t.
  Proof. apply (fixpoint_unfold IT_rec_pre). Qed.
  Lemma IT_rec2_unfold t :
    IT_rec2 t ≡ (IT_rec_pre IT_rec).2 t.
  Proof. apply (fixpoint_unfold IT_rec_pre). Qed.

  (** ** Some computational rules *)
  Lemma IT_rec1_ret (n : A) :
    IT_rec1 (Ret n) ≡ Pret n.
  Proof.
    rewrite IT_rec1_unfold /IT_rec_pre.
    cbn-[sumO_rec].
    (* Here we need to be careful not to simplify sum_rec, which will
    unfold into a `match` and we wouldnt be able to use setoid
    rewriting. *)
    rewrite IT_unfold_fold. reflexivity.
  Qed.

  Lemma IT_rec1_err e :
    IT_rec1 (Err e) ≡ Perr e.
  Proof.
    rewrite IT_rec1_unfold.
    rewrite /IT_rec_pre.
    cbn-[sumO_rec].
    rewrite IT_unfold_fold; reflexivity.
  Qed.

  Lemma IT_rec1_tau t :
    IT_rec1 (Tau t) ≡ Ptau (laterO_map (prod_in idfun IT_rec1) t).
  Proof.
    rewrite IT_rec1_unfold.
    rewrite /IT_rec_pre.
    cbn-[sumO_rec].
    rewrite IT_unfold_fold; reflexivity.
  Qed.

  Program Definition sandwich : (IT E A -n> IT E A) -n> sumO (IT E A) P -n> prodO (IT E A) P :=
    λne f, prod_in idfun IT_rec1 ◎ f ◎ sumO_rec idfun IT_rec2.
  Next Obligation. solve_proper. Defined.
  Program Definition unsandwich : (sumO (IT E A) P -n> prodO (IT E A) P) -n> IT E A -n> IT E A :=
    λne f, fstO ◎ f ◎ inlO.
  Next Obligation. solve_proper. Defined.

  Lemma sandwich_unsandwich :
    unsandwich ◎ sandwich ≡ idfun.
  Proof. intros f x; reflexivity. Qed.


  Lemma IT_rec1_fun f :
    IT_rec1 (Fun f) ≡ Parr (laterO_map sandwich f).
  Proof.
    rewrite IT_rec1_unfold.
    rewrite /IT_rec_pre.
    cbn-[sumO_rec].
    rewrite IT_unfold_fold.
    simpl. f_equiv.
    unfold sandwich. repeat f_equiv.
    intros g x. cbn-[sumO_rec].
    destruct x as [x|x]; simpl; eauto.
  Qed.

  Lemma IT_rec1_vis op i k  :
    let s_in := oFunctor_map (Ins (E op)) (sumO_rec idfun IT_rec2,prod_in idfun IT_rec1) in
    let s_out := oFunctor_map (Outs (E op)) (prod_in idfun IT_rec1,sumO_rec idfun IT_rec2) in
    IT_rec1 (Vis op i k) ≡
      Pvis op (s_in i) (laterO_map (prod_in idfun IT_rec1) ◎ k ◎ s_out).
  Proof.
    simpl. rewrite IT_rec1_unfold.
    unfold IT_rec_pre. cbn-[sumO_rec].
    rewrite IT_unfold_fold.
    simpl. repeat f_equiv; try reflexivity.
  Qed.

End IT_rec.
Arguments IT_rec {_ _ _} P {_ _} _ _ _ _ _ _.
Arguments sandwich {_ _ _} _ {_ _ _ _ _ _ _ _}.

 (* exercise: show that every P with the properties above must have a bottom element and that it_rec maps bottom to bottom  *)
(** XXX ***) Opaque prod_in.
(* needed for the followin proof *)
Global Instance Pvis_rec_ne {E A} `{!Cofe A} {P: ofe} `{!Cofe P, !Inhabited P} n :
  Proper ((forall_relation (λ _, (dist n))) ==> (dist_later n) ==> (dist n)) (Pvis_rec (E:=E) (A:=A) P).
Proof.
  intros v1 v2 Hv [h1 h2] [g1 g2] Hhg.
  intros [op [i k]].
  unfold Pvis_rec. simpl.
  specialize (Hv op). simpl in Hv.
  f_equiv; eauto.
  - f_equiv; eauto.
    apply opInterp_ins_contractive; eauto.
    destruct n; first by eauto using dist_later_0.
    apply dist_later_S. apply dist_later_S in Hhg. simpl in *; destruct Hhg; split; simpl; f_equiv; eauto.
  - intro a. simpl. repeat (f_contractive || f_equiv); simpl in *; destruct Hhg; eauto.
Qed.

#[export]  Instance Pvis_rec_proper {E A} `{!Cofe A} {P: ofe} `{!Cofe P, !Inhabited P} :
  Proper ((forall_relation (λ _, (equiv))) ==> (equiv) ==> (equiv)) (Pvis_rec (E:=E) (A:=A) P).
Proof.
  intros v1 v2 Hv [h1 h2] [g1 g2] [Hhg1 Hhg2].
  intros [op [i k]].
  unfold Pvis_rec. simpl.
  specialize (Hv op). simpl in Hv. solve_proper.
Qed.
(** XXX ***) Transparent prod_in.

Global Instance IT_rec_ne {E} {A} `{!Cofe A} {P: ofe}  `{!Cofe P, !Inhabited P} n :
  Proper ((pointwise_relation _ (dist n)) ==> (dist n) ==> (dist n) ==> (dist n) ==>
   (forall_relation (λ _, dist n)) ==>
   (dist n) ==> (dist n)) (IT_rec P (E:=E) (A:=A)).
Proof.
  intros nt1 nt2 Hnt e1 e2 He th1 th2 Hth a1 a2 Ha v1 v2 Hv unf1 unf2 Hunf.
  unfold IT_rec.
  eapply fixpoint_ne. intros [h k].
  unfold IT_rec_pre.
  repeat f_equiv; intro; eauto.
Qed.

Global Instance IT_rec_proper {E} {A} `{!Cofe A} {P: ofe}  `{!Cofe P, !Inhabited P} :
  Proper ((pointwise_relation _ equiv) ==> (equiv) ==> (equiv) ==> (equiv) ==>
   (forall_relation (λ _, equiv)) ==>
   (equiv) ==> (equiv)) (IT_rec P (E:=E) (A:=A)).
Proof.
  intros nt1 nt2 Hnt e1 e2 He th1 th2 Hth a1 a2 Ha v1 v2 Hv unf1 unf2 Hunf.
  unfold IT_rec.
  eapply fixpoint_proper. intros [h k].
  unfold IT_rec_pre.
  repeat f_equiv; intro; eauto.
Qed.


Global Instance IT_rec1_ne {E A} `{!Cofe A} {P : ofe} `{!Cofe P, !Inhabited P} n :
  Proper ((pointwise_relation _ (dist n)) ==> (dist n) ==> (dist n) ==> (dist n) ==>
   (forall_relation (λ _, dist n)) ==>
   (dist n) ==> (dist n)) (IT_rec1 P (E:=E) (A:=A)).
Proof.
  unfold IT_rec1.
  intros nt1 nt2 Hnt e1 e2 He th1 th2 Hth a1 a2 Ha v1 v2 Hv unf1 unf2 Hunf.
  f_equiv.
  apply IT_rec_ne; eauto.
Qed.
Global Instance IT_rec1_proper {E A} `{!Cofe A} {P: ofe}  `{!Cofe P, !Inhabited P} :
  Proper ((pointwise_relation _ (equiv)) ==> (equiv) ==> (equiv) ==> (equiv) ==>
   (forall_relation (λ _, equiv)) ==>
   (equiv) ==> (equiv)) (IT_rec1 P (E:=E) (A:=A)).
Proof.
  unfold IT_rec1.
  intros nt1 nt2 Hnt e1 e2 He th1 th2 Hth a1 a2 Ha v1 v2 Hv unf1 unf2 Hunf.
  f_equiv.
  apply IT_rec_proper; eauto.
Qed.

Global Instance IT_rec2_ne {E A} `{!Cofe A} {P : ofe} `{!Cofe P, !Inhabited P} n :
  Proper ((pointwise_relation _ (dist n)) ==> (dist n) ==> (dist n) ==> (dist n) ==>
   (forall_relation (λ _, dist n)) ==>
   (dist n) ==> (dist n)) (IT_rec2 P (E:=E) (A:=A)).
Proof.
  unfold IT_rec2.
  intros nt1 nt2 Hnt e1 e2 He th1 th2 Hth a1 a2 Ha v1 v2 Hv unf1 unf2 Hunf.
  f_equiv.
  apply IT_rec_ne; eauto.
Qed.

(** iteration 'helpers', turn recursors into iterators *)
Section iter.
  Context {E : opsInterp}.
  Context {A} `{!Cofe A}.
  Local Notation IT := (IT E A).
  Variable (P : ofe).
  Context `{!Cofe P}.

  Program Definition Iter_Arr :
    laterO (sumO IT P -n> prodO IT P) -n> laterO (P -n> P)
    := laterO_map (λne f, sndO ◎ f ◎ inrO).
  Next Obligation. solve_proper. Qed.

  Definition Iter_Tau :
    laterO (prodO IT P) -n> laterO P := laterO_map sndO.

  Program Definition Orig_Arr :
    laterO (sumO IT P -n> prodO IT P) -n> laterO (IT -n> IT)
    := laterO_map (λne f, fstO ◎ f ◎ inlO).
  Next Obligation. solve_proper. Qed.

  Definition Orig_Tau :
    laterO (prodO IT P) -n> laterO IT := laterO_map fstO.

  Definition Orig_Vis_Inp op :
    (oFunctor_car (Ins (E op)) (sumO IT P) (prodO IT P)) -n>
    (oFunctor_apply (Ins (E op)) IT)
    := oFunctor_map _ (inlO,fstO).

  Program Definition Orig_Vis_Cont op :
    (oFunctor_car (Outs (E op)) (prodO IT P) (sumO IT P) -n> laterO (prodO IT P)) -n>
    (oFunctor_apply (Outs (E op)) IT -n> laterO IT)
    := λne k, laterO_map fstO ◎ k ◎ oFunctor_map _ (fstO,inlO).
  Next Obligation. solve_proper. Qed.
End iter.

(** * Ticks/later-algebra structure *)
Section ticks.
  Context {E : opsInterp}.
  Context {A} `{!Cofe A}.
  Local Notation IT := (IT E A).
  Definition Tick : IT -n> IT := Tau ◎ NextO.
  Program Definition Tick_n n : IT -n> IT :=
    λne t, Nat.iter n Tick t.
  Next Obligation.
    induction n; solve_proper.
  Qed.
  Global Instance IT_tick_proper n : Proper ((≡) ==> (≡)) (Tick_n n).
  Proof. induction n; solve_proper. Qed.
  Global Instance Tick_inj k : Inj (dist k) (dist (S k)) Tick.
  Proof.
    intros x y. intros H1.
    assert (IT_unfold (Tick x) ≡{S k}≡ IT_unfold (Tick y)) as H2.
    { by rewrite H1. }
    revert H2. rewrite /Tick /=.
    rewrite !IT_unfold_fold. intros H2.
    apply (Next_inj (S k) x y); last lia.
    by eapply inr_ne_inj, inl_ne_inj.
  Qed.
  Global Instance Tick_contractive : Contractive Tick.
  Proof. solve_contractive. Qed.

  Lemma Tick_eq α : Tick α ≡ Tau (Next α).
  Proof. reflexivity. Qed.

  Lemma Tick_n_O α : Tick_n 0 α = α.
  Proof. reflexivity. Qed.

  Lemma Tick_n_S k α : Tick_n (S k) α = Tick (Tick_n k α).
  Proof. reflexivity. Qed.

  Lemma Tick_n_S' k α : Tick_n (S k) α = Tick_n k (Tick α).
  Proof.
    induction k; first reflexivity.
    rewrite Tick_n_S. rewrite IHk. done.
  Qed.

  Lemma Tick_add k l α : Tick_n (k + l) α = Tick_n k (Tick_n l α).
  Proof.
    induction k; first done.
    cbn[plus]. by rewrite !Tick_n_S IHk.
  Qed.

  Lemma IT_ret_tick_ne k α {PROP : bi} `{!BiInternalEq PROP} :
    (Ret k ≡ Tick α ⊢ False : PROP)%I.
  Proof. apply IT_ret_tau_ne. Qed.
  Lemma IT_fun_tick_ne f α {PROP : bi} `{!BiInternalEq PROP} :
    (Fun f ≡ Tick α ⊢ False : PROP)%I.
  Proof. apply IT_fun_tau_ne. Qed.
  Lemma IT_tick_vis_ne α op i k {PROP : bi} `{!BiInternalEq PROP} :
    (Tick α ≡ Vis op i k ⊢ False : PROP)%I.
  Proof. apply IT_tau_vis_ne. Qed.
  Lemma IT_tick_err_ne α e {PROP : bi} `{!BiInternalEq PROP} :
    (Tick α ≡ Err e ⊢ False : PROP)%I.
  Proof. apply IT_tau_err_ne. Qed.

  #[export] Instance from_modal_tick x y      {PROP : bi} `{!BiInternalEq PROP} :
    FromModal (PROP1:=PROP) (PROP2:=PROP) True (modality_instances.modality_laterN 1)
              (▷ (x ≡ y) : PROP)%I (Tick x ≡ Tick y) (x ≡ y).
  Proof.
    rewrite /FromModal => _. cbn-[Tick]. apply f_equivI_contractive.
    apply _.
  Qed.

  #[export] Instance into_laterN_tick only_head n n' (α β : IT)
    {PROP : bi} `{!BiInternalEq PROP} :
    nat_cancel.NatCancel n 1 n' 0 →
    IntoLaterN (PROP:=PROP) only_head n (Tick α ≡ Tick β) (α ≡ β) | 2.
  Proof.
    rewrite /IntoLaterN /MaybeIntoLaterN.
    move=> H.
    rewrite -Tau_inj'.
    by eapply (class_instances_internal_eq.into_laterN_Next only_head).
  Qed.

  (** ** No cofusion principle *)
  Lemma IT_dont_confuse (α : IT):
       (∃ e,      α ≡ Err e)
     ∨ (∃ n,      α ≡ Ret n)
     ∨ (∃ f,      α ≡ Fun f)
     ∨ (∃ β,      α ≡ Tick β)
     ∨ (∃ op i k, α ≡ Vis op i k).
  Proof.
    remember (IT_unfold α) as ua.
    assert (IT_fold ua ≡ α) as Hfold.
    { rewrite Hequa. apply IT_fold_unfold. }
    destruct ua as [ [ [ [ n | f ] | e ] | la ] | [op [i k] ]].
    - right. left. exists n. done.
    - right. right. left. exists f. done.
    - left. exists e. done.
    - right. right. right. left.
      destruct (Next_uninj la) as [β Hb].
      exists β. rewrite -Hfold Hb. done.
    - right. right. right. right. exists op,i,k. done.
  Qed.

  Lemma IT_dont_confuse' (α : IT) {PROP : bi} `{!BiInternalEq PROP} :
    (⊢ (∃ e,      α ≡ Err e)
     ∨ (∃ n,      α ≡ Ret n)
     ∨ (∃ f,      α ≡ Fun f)
     ∨ (∃ β,      α ≡ Tick β)
     ∨ (∃ op i k, α ≡ Vis op i k)
      : PROP)%I.
  Proof.
    remember (IT_unfold α) as ua.
    assert (IT_fold ua ≡ α) as Hfold.
    { rewrite Hequa. apply IT_fold_unfold. }
    destruct ua as [ [ [ [ n | f ] | e ] | la ] | [op [i k] ]].
    - iRight. iLeft. iExists n. done.
    - iRight. iRight. iLeft. iExists f. done.
    - iLeft. iExists e. done.
    - iRight. iRight. iRight. iLeft.
      destruct (Next_uninj la) as [β Hb].
      iExists β. rewrite -Hfold Hb. done.
    - iRight. iRight. iRight. iRight. iExists op,i,k. done.
  Qed.

End ticks.

(** semantic "values" *)
Section ITV.
  Context {E : opsInterp}.
  Context {A} `{!Cofe A}.
  Local Notation IT := (IT E A).
  Local Opaque Ret Fun.

  (** We describe "semantic values" separately, so that we can reason about the easier *)
  Inductive ITV :=
  | RetV : A → ITV
  | FunV : laterO (IT -n> IT) → ITV
  .

  Definition IT_of_V : ITV → IT := λ v,
      match v with
      | RetV n => Ret n
      | FunV f => Fun f
      end.

  #[export] Instance ITV_inhabited : Inhabited ITV := populate (FunV (Next idfun)).

  #[export] Instance ITV_dist : Dist (ITV)
    := λ n αv βv, match αv, βv with
                  | RetV x, RetV y => dist n x y
                  | FunV f, FunV g => dist n f g
                  | _, _ => False
                  end.
  #[export] Instance ITV_dist_equiv n : Equivalence (@dist ITV _ n).
  Proof.
    unfold dist.
    split.
    - intros [|f]; simpl; eauto.
    - intros [n1|f1] [n2|f2]; simpl; eauto.
    - intros [n1|f1] [n2|f2] [n3|f3]; simpl; try naive_solver.
      + apply transitivity.
      + apply transitivity.
  Qed.
  #[export] Instance ITV_equiv : Equiv ITV :=
    λ αv βv, match αv, βv with
             | RetV n, RetV m => n ≡ m
             | FunV f, FunV g => f ≡ g
             | _, _ => False
             end.
  #[export] Instance ITV_equiv_equiv : Equivalence (≡@{ITV}).
  Proof.
    unfold equiv.
    split.
    - intros [|f]; simpl; eauto.
    - intros [n1|f1] [n2|f2]; simpl; eauto.
    - intros [n1|f1] [n2|f2] [n3|f3]; simpl; try naive_solver;
      apply transitivity.
  Qed.
  Lemma ITV_equiv_dist (x y : ITV) :
    x ≡ y ↔ ∀ n, x ≡{n}≡ y.
  Proof.
    unfold equiv, dist.
    destruct x as [n1|f1], y as [n2|f2]; simpl; eauto using equiv_dist;
      try naive_solver.
    + split; first tauto.
      intros H. apply (H 0).
    + split; first tauto.
      intros H. apply (H 0).
  Qed.
  Lemma ITV_dist_lt n m (x y : ITV) :
    x ≡{n}≡ y → m < n → x ≡{m}≡ y.
  Proof.
    unfold dist.
    destruct x as [n1|f1], y as [n2|f2]; simpl; eauto using dist_lt.
  Qed.

  Canonical Structure ITVO := Ofe ITV ({| mixin_equiv_dist := ITV_equiv_dist;
                                mixin_dist_lt := ITV_dist_lt;
                                mixin_dist_equivalence := ITV_dist_equiv
                                       |}).

  #[local] Definition sum_to_ITV : sum A (later (IT -n> IT)) → ITV :=
    λ x, match x with
         | inl n => RetV n
         | inr f => FunV f
         end.
  #[local] Definition ITV_to_sum : ITV → sum A (later (IT -n> IT)) :=
    λ x, match x with
         | RetV n => inl n
         | FunV f => inr f
         end.
  #[export] Instance ITV_cofe : Cofe ITV.
  Proof.
    simple refine (iso_cofe (A:=sumO A (laterO (IT -n> IT))) sum_to_ITV ITV_to_sum _ _).
    - intros n [n1|f1] [n2|f2]; simpl.
      all: split; try by (inversion 1; naive_solver).
      + intros Hf. f_equiv. done.
      + intros Hf. f_equiv. done.
    - intros [n|f]; simpl; done.
  Qed.

  #[export] Instance IT_of_V_ne : NonExpansive IT_of_V.
  Proof.
    intro n. rewrite {1}/dist.
    intros [n1|f1] [n2|f2]; simpl.
    all: try naive_solver.
    + apply Ret.
    + apply Fun.
  Qed.
  #[export] Instance IT_of_V_proper : Proper ((≡) ==> (≡)) IT_of_V.
  Proof.
    intros [n1|f1] [n2|f2]; simpl.
    all: try solve_proper.
    all: try inversion 1.
  Qed.
  #[export] Instance FunV_ne : NonExpansive FunV.
  Proof. solve_proper. Qed.
  #[export] Instance FunV_proper : Proper ((≡) ==> (≡)) FunV.
  Proof. solve_proper. Qed.
  #[export] Instance RetV_ne : NonExpansive RetV.
  Proof. solve_proper. Qed.
  #[export] Instance RetV_proper : Proper ((≡) ==> (≡)) RetV.
  Proof. solve_proper. Qed.

  Class AsVal (α : IT) := as_val : ∃ v, IT_of_V v ≡ α.
  Class IntoVal (α : IT) (αv : ITV) := into_val : IT_of_V αv ≡ α.

  #[export] Instance asval_ret n : AsVal (Ret n).
  Proof. exists (RetV n). reflexivity. Qed.
  #[export] Instance asval_fun n : AsVal (Fun n).
  Proof. exists (FunV n). reflexivity. Qed.
  #[export] Instance asval_of_V v : AsVal (IT_of_V v).
  Proof. exists v. reflexivity. Qed.
  (* since this is a typeclass, meant to be used at the Coq level,
   we dont need the non-expansiveness *)
  #[export] Instance asval_proper : Proper ((≡) ==> impl) AsVal.
  Proof.
    unfold AsVal.
    intros x y Hxy [v Hx]. exists v. by rewrite Hx.
  Qed.

  #[export] Instance intoval_ret n : IntoVal (Ret n) (RetV n).
  Proof. unfold IntoVal. simpl. reflexivity. Qed.
  #[export] Instance intoval_fun f : IntoVal (Fun f) (FunV f).
  Proof. unfold IntoVal. simpl. reflexivity. Qed.
  #[export] Instance intoval_of_V v : IntoVal (IT_of_V v) v.
  Proof. unfold IntoVal. reflexivity. Qed.
  #[export] Instance intoval_proper : Proper ((≡) ==> (≡) ==> impl) IntoVal.
  Proof.
    unfold IntoVal.
    intros x y Hxy v1 v2 Hv Hx.
    by rewrite -Hv -Hxy.
  Qed.


  Program Definition None1 {A B} : A -n> optionO B := λne _, None.
  Program Definition None2 {A B C} : A -n> B -n> optionO C := λne _ _, None.
  Program Definition SomeO {A} : A -n> optionO A := OfeMor Some.

  Program Definition IT_to_V : IT -n> optionO ITV
    := IT_rec1 (optionO ITV)
               (λ e, None)
               (SomeO ◎ OfeMor RetV)
               (SomeO ◎ OfeMor FunV ◎ Orig_Arr _)
               None1
               (λ _, None2)
               _.
  Next Obligation.
    simple refine (inlO ◎ inlO ◎ inrO ◎ _).
    simple refine (λne _, RuntimeErr).
  Qed.

  Lemma IT_to_V_Ret n : IT_to_V (Ret n) ≡ Some $ RetV n.
  Proof. apply IT_rec1_ret. Qed.
  Lemma IT_to_V_Fun f : IT_to_V (Fun f) ≡ Some $ FunV f.
  Proof.
    rewrite IT_rec1_fun /=. f_equiv. f_equiv.
    unfold Orig_Arr. rewrite -laterO_map_compose.
    etrans; last by apply laterO_map_id.
    do 2 f_equiv. intros g x. done.
  Qed.
  Lemma IT_to_V_Err e : IT_to_V (Err e) ≡ None.
  Proof. apply IT_rec1_err. Qed.
  Lemma IT_to_V_Tau la : IT_to_V (Tau la) ≡ None.
  Proof. apply IT_rec1_tau. Qed.
  Lemma IT_to_V_Tick α : IT_to_V (Tick α) ≡ None.
  Proof. apply IT_to_V_Tau. Qed.
  Lemma IT_to_V_Vis op i k : IT_to_V (Vis op i k) ≡ None.
  Proof. apply IT_rec1_vis. Qed.

  Lemma IT_to_of_V v : IT_to_V (IT_of_V v) ≡ Some v.
  Proof.
    destruct v; simpl.
    - apply IT_to_V_Ret.
    - apply IT_to_V_Fun.
  Qed.

  Lemma IT_of_to_V α v {PROP : bi} `{!BiInternalEq PROP} :
    (IT_to_V α ≡ Some v ⊢ IT_of_V v ≡ α : PROP).
  Proof.
    iIntros "H".
    iPoseProof (IT_dont_confuse' α) as "Ha".
    iDestruct "Ha" as "[Ha | [Ha | [ Ha | [ Ha | Ha ]]]]".
    - iDestruct "Ha" as (e) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Err.
      iPoseProof (option_equivI with "H") as "H". done.
    - iDestruct "Ha" as (n) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Ret.
      iPoseProof (option_equivI with "H") as "H".
      iRewrite -"H". by iApply internal_eq_sym.
    - iDestruct "Ha" as (f) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Fun.
      iPoseProof (option_equivI with "H") as "H".
      iRewrite -"H". by iApply internal_eq_sym.
    - iDestruct "Ha" as (lf) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Tau.
      iPoseProof (option_equivI with "H") as "H". done.
    - iDestruct "Ha" as (op i k) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Vis.
      iPoseProof (option_equivI with "H") as "H". done.
  Qed.

  Lemma IT_of_to_V' α v : IT_to_V α ≡ Some v → IT_of_V v ≡ α.
  Proof.
    destruct (IT_dont_confuse α)
      as [[e Ha2] | [[m Ha2] | [ [g Ha2] | [[la Ha2]|[op [i [k Ha2]]]] ]]].
    all: rewrite Ha2.
    - rewrite IT_to_V_Err.
      rewrite option_equiv_Forall2. inversion 1.
    - rewrite IT_to_V_Ret.
      rewrite option_equiv_Forall2. inversion 1 as [x y Hxy|].
      simplify_eq/=. rewrite -Hxy.
      done.
    - rewrite IT_to_V_Fun.
      rewrite option_equiv_Forall2. inversion 1 as [x y Hxy|].
      simplify_eq/=. rewrite -Hxy.
      done.
    - rewrite IT_to_V_Tick.
      rewrite option_equiv_Forall2. inversion 1.
    - rewrite IT_to_V_Vis.
      rewrite option_equiv_Forall2. inversion 1.
  Qed.

  Lemma IT_to_V_None α {PROP : bi} `{!BiInternalEq PROP} :
    (IT_to_V α ≡ None ⊢ (∃ e, α ≡ Err e)
                     ∨ (∃ β, α ≡ Tick β)
                     ∨ (∃ op i k, α ≡ Vis op i k)
      : PROP)%I.
  Proof.
    iIntros "H".
    iPoseProof (IT_dont_confuse' α) as "Ha".
    iDestruct "Ha" as "[Ha | [Ha | [ Ha | [ Ha | Ha ]]]]"; eauto with iFrame.
    - iDestruct "Ha" as (n) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Ret.
      iPoseProof (option_equivI with "H") as "H".
      done.
    - iDestruct "Ha" as (f) "Ha".
      iRewrite "Ha" in "H". rewrite IT_to_V_Fun.
      iPoseProof (option_equivI with "H") as "H".
      done.
  Qed.

  Lemma IT_of_V_inj' αv βv {PROP : bi} `{!BiInternalEq PROP} :
    (IT_of_V αv ≡ IT_of_V βv ⊢ αv ≡ βv : PROP)%I.
  Proof.
    iIntros "H".
    destruct αv as [n1|f1], βv as [n2|f2]; simpl.
    - iPoseProof (Ret_inj' with"H") as"H".
      by iRewrite "H". (*XXX: easier proof?*)
    - iExFalso. iApply (IT_ret_fun_ne with "H").
    - iExFalso. iApply (IT_ret_fun_ne). iApply internal_eq_sym.
      iExact "H".
    - iPoseProof (Fun_inj' with "H") as "H".
      by iRewrite "H".
  Qed.

End ITV.
Arguments ITV E A {_}.

(** * Destructors / matching *)
Section IT_destructors.
  Context {E : opsInterp}.
  Context {A} `{!Cofe A}.
  Local Notation IT := (IT E A).

  Definition Err1 {B : ofe} : B -n> IT :=
    λne _, Err RuntimeErr.
  Definition Err2 {B C : ofe} : B -n> C -n> IT :=
    λne _ _, Err RuntimeErr.

  (** Don't touch the input, but recuse on the result of the continuation, this should be called Vis_iter or something *)
  Program Definition Vis_ (op : opid E)  :
    (oFunctor_car (Ins (E op)) (sumO IT IT) (prodO IT IT)) -n>
    ((oFunctor_car (Outs (E op)) (prodO IT IT) (sumO IT IT)) -n> laterO (prodO IT IT)) -n> IT
    := λne i k, Vis op
                    (oFunctor_map _ (inlO,fstO) i)
                    (laterO_map sndO ◎ k ◎ oFunctor_map _ (fstO,inlO)).
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  Definition get_ret (f : A -n> IT)
    : IT -n> IT
    := IT_rec1 IT
               Err (* error *)
               f (* nat *)
               Err1 (* function *)
               (Tau ◎ Iter_Tau _) (* step *)
               Vis_
               IT_unfold.

  Definition get_fun (f : laterO (IT -n> IT) -n> IT)
    : IT -n> IT
    := IT_rec1 IT
               Err (* error *)
               Err1 (* nat *)
               (f ◎ laterO_map (unsandwich _)) (* function *)
               (Tau ◎ Iter_Tau _) (* recurse on step *)
               Vis_
               IT_unfold.

  Definition get_val (f : IT -n> IT)
    : IT -n> IT
    := IT_rec1 IT
               Err (* error *)
               (f ◎ Ret) (* nat *)
               (f ◎ Fun ◎ laterO_map (unsandwich _)) (* function *)
               (Tau ◎ Iter_Tau _) (* recurse on step *)
               Vis_
               IT_unfold.

  Global Instance get_fun_ne : NonExpansive get_fun.
  Proof.
    repeat intro. unfold get_fun.
    (*why doesnt f_equiv work here?*)
    apply IT_rec1_ne; solve_proper.
  Qed.
  Global Instance get_ret_ne : NonExpansive get_ret.
  Proof.
    repeat intro. unfold get_ret.
    (*why doesnt f_equiv work here?*)
    apply IT_rec1_ne; solve_proper.
  Qed.
  Global Instance get_val_ne n : Proper (((dist n)) ==> (dist n)) get_val.
  Proof.
    repeat intro. unfold get_val.
    (*why doesnt f_equiv work here?*)
    apply IT_rec1_ne; solve_proper.
  Qed.
  Global Instance get_fun_proper : Proper ((≡) ==> (≡)) get_fun.
  Proof.
    repeat intro. unfold get_fun.
    (*why doesnt f_equiv work here?*)
    apply IT_rec1_proper; solve_proper.
  Qed.
  Global Instance get_val_proper : Proper ((≡) ==> (≡)) get_val.
  Proof.
    repeat intro. unfold get_val.
    (*why doesnt f_equiv work here?*)
    apply IT_rec1_proper; solve_proper.
  Qed.
  Global Instance get_ret_proper : Proper ((≡) ==> (≡)) get_ret.
  Proof.
    repeat intro. unfold get_ret.
    (*why doesnt f_equiv work here?*)
    apply IT_rec1_proper; solve_proper.
  Qed.


  Program Definition get_ret2 (f : A -n> A -n> IT) : IT -n> IT -n> IT := λne x y,
      get_ret (λne x, get_ret (λne y, f x y) y) x.
  Solve All Obligations with solve_proper_please.
  Global Instance get_ret2_ne : NonExpansive get_ret2.
  Proof.
    intros n f1 f2 Hf. unfold get_ret2.
    intros x y. simpl. apply get_ret_ne.
    clear x. intros x. simpl. apply get_ret_ne.
    clear y. intros y. simpl. apply Hf.
  Qed.
  Global Instance get_ret2_proper : Proper ((≡) ==> (≡)) get_ret2.
  Proof. apply ne_proper. apply _. Qed.

  Lemma get_ret_err f e : get_ret f (Err e) ≡ Err e.
  Proof. by rewrite IT_rec1_err. Qed.
  Lemma get_ret_fun f g : get_ret f (Fun g) ≡ Err RuntimeErr.
  Proof. by rewrite IT_rec1_fun. Qed.
  Lemma get_ret_ret f n : get_ret f (Ret n) ≡ f n.
  Proof. by rewrite IT_rec1_ret. Qed.
  Lemma get_ret_tick f t : get_ret f (Tick t) ≡ Tick (get_ret f t).
  Proof.
    Opaque Tau.
    rewrite IT_rec1_tau.
    cbn-[prod_in]. f_equiv.
    rewrite -laterO_map_compose. simpl. done.
  Qed.
  Lemma get_ret_tick_n f n t : get_ret f (Tick_n n t) ≡ Tick_n n (get_ret f t).
  Proof.
    induction n; first reflexivity.
    rewrite get_ret_tick. by rewrite IHn.
  Qed.
  Lemma get_ret_vis f op i k : get_ret f (Vis op i k) ≡ Vis op i (laterO_map (get_ret f) ◎ k).
  Proof.
    rewrite IT_rec1_vis. cbn-[prod_in]. f_equiv.
    - rewrite -oFunctor_map_compose.
      etrans. 2:{ eapply oFunctor_map_id. }
      repeat f_equiv.
      + intro x. reflexivity.
      + intro x. reflexivity.
    - intros x. cbn-[prod_in].
      rewrite -laterO_map_compose.
      rewrite -oFunctor_map_compose.
      f_equiv.
      + f_equiv. intros y. simpl. done.
      + f_equiv.
        etrans. 2:{ eapply oFunctor_map_id. }
        repeat f_equiv.
        * intros ?; done.
        * intros y. simpl. done.
  Qed.

  Lemma get_val_err f e : get_val f (Err e) ≡ Err e.
  Proof. by rewrite IT_rec1_err. Qed.
  Lemma get_val_ret f n : get_val f (Ret n) ≡ f (Ret n).
  Proof. by rewrite IT_rec1_ret. Qed.
  Lemma get_val_fun f g : get_val f (Fun g) ≡ f (Fun g).
  Proof.
    rewrite IT_rec1_fun.
    cbn-[Fun]. rewrite -laterO_map_compose.
    trans (f (Fun (laterO_map idfun g))).
    { repeat f_equiv. apply sandwich_unsandwich. }
    by rewrite laterO_map_id.
  Qed.
  Lemma get_val_ITV' f βv : get_val f (IT_of_V βv) ≡ f (IT_of_V βv).
  Proof.
    destruct βv; simpl.
    - rewrite get_val_ret//.
    - rewrite get_val_fun//.
  Qed.
  Lemma get_val_ITV `{!AsVal β} f : get_val f β ≡ f β.
  Proof. destruct (_ : AsVal β) as [bv <-]. apply get_val_ITV'. Qed.
  Lemma get_val_tick f t : get_val f (Tick t) ≡ Tick $ get_val f t.
  Proof.
    rewrite IT_rec1_tau.
    cbn-[prod_in]. f_equiv.
    rewrite -laterO_map_compose. reflexivity.
  Qed.
  Lemma get_val_tick_n f n t : get_val f (Tick_n n t) ≡ Tick_n n $ get_val f t.
  Proof.
    induction n; first reflexivity.
    rewrite get_val_tick. by rewrite IHn.
  Qed.
  Lemma get_val_vis f op i k : get_val f (Vis op i k) ≡ Vis op i (laterO_map (get_val f) ◎ k).
  Proof.
    rewrite IT_rec1_vis. cbn-[prod_in]. f_equiv.
    - rewrite -oFunctor_map_compose.
      etrans. 2:{ eapply oFunctor_map_id. }
      repeat f_equiv.
      + intro x. reflexivity.
      + intro x. reflexivity.
    - intros x. cbn-[prod_in].
      rewrite -laterO_map_compose.
      rewrite -oFunctor_map_compose.
      f_equiv.
      + f_equiv. intros y. simpl. done.
      + f_equiv.
        etrans. 2:{ eapply oFunctor_map_id. }
        repeat f_equiv.
        * intros ?; done.
        * intros y. simpl. done.
  Qed.

  Lemma get_fun_err f e : get_fun f (Err e) ≡ Err e.
  Proof. by rewrite IT_rec1_err. Qed.
  Lemma get_fun_fun f g : get_fun f (Fun g) ≡ f g.
  Proof.
    rewrite IT_rec1_fun.
    simpl. rewrite -laterO_map_compose.
    trans (f (laterO_map idfun g)).
    { repeat f_equiv. apply sandwich_unsandwich. }
    by rewrite laterO_map_id.
  Qed.
  Lemma get_fun_ret f n : get_fun f (Ret n) ≡ Err RuntimeErr.
  Proof. by rewrite IT_rec1_ret. Qed.

  Lemma get_fun_vis f op i k : get_fun f (Vis op i k) ≡ Vis op i (laterO_map (get_fun f) ◎ k).
  Proof.
    rewrite IT_rec1_vis. cbn-[prod_in]. f_equiv.
    - rewrite -oFunctor_map_compose.
      etrans. 2:{ eapply oFunctor_map_id. }
      repeat f_equiv.
      + intro x. reflexivity.
      + intro x. reflexivity.
    - intros x. cbn-[prod_in].
      rewrite -laterO_map_compose.
      rewrite -oFunctor_map_compose.
      f_equiv.
      + f_equiv. intros y. simpl. done.
      + f_equiv.
        etrans. 2:{ eapply oFunctor_map_id. }
        repeat f_equiv.
        * intros ?; done.
        * intros y. simpl. done.
  Qed.

  Lemma get_fun_tick f t : get_fun f (Tick t) ≡ Tick (get_fun f t).
  Proof.
    Opaque Tau.
    rewrite IT_rec1_tau.
    cbn-[prod_in]. f_equiv.
    rewrite -laterO_map_compose. reflexivity.
  Qed.
  Lemma get_fun_tick_n f t n : get_fun f (Tick_n n t) ≡ Tick_n n (get_fun f t).
  Proof.
    induction n; first reflexivity.
    by rewrite get_fun_tick IHn.
  Qed.
End IT_destructors.


(** * Homomorphisms of ITs *)
Section it_hom.
  Context {E : opsInterp}.
  Context {A} `{!Cofe A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Class IT_hom (f : IT → IT) := IT_HOM {
      hom_ne :: NonExpansive f;
      hom_tick: ∀ α, f (Tick α) ≡ Tick (f α);
      hom_vis : ∀ op i ko, f (Vis op i ko) ≡ Vis op i (laterO_map (OfeMor f) ◎ ko);
      hom_err : ∀ e, f (Err e) ≡ Err e
    }.
  #[export] Instance IT_hom_proper f `{!IT_hom f} : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper. apply _. Qed.

  #[export] Instance IT_hom_compose f g : IT_hom f → IT_hom g → IT_hom (f ∘ g).
  Proof.
    intros Hf Hg. simple refine (IT_HOM _ _ _ _ _).
    - intros a. simpl. rewrite !hom_tick//.
    - intros op i k. simpl. rewrite !hom_vis//.
      f_equiv. intro x. simpl. rewrite -laterO_map_compose//.
    - intro e. cbn-[Err]. rewrite !hom_err//.
  Qed.
  #[export] Instance IT_hom_idfun : IT_hom idfun.
  Proof.
    simple refine (IT_HOM _ _ _ _ _); simpl; eauto.
    intros op i k. f_equiv. intro x. simpl.
    by rewrite laterO_map_id.
  Qed.

  Lemma hom_tick_n n f (α : IT) `{!IT_hom f} : f (Tick_n n α) ≡ Tick_n n (f α).
  Proof.
    revert α. induction n=>α; cbn-[Tick]; eauto.
    rewrite hom_tick. f_equiv. by apply IHn.
  Qed.

  Lemma IT_hom_val_inv α f `{!IT_hom f} :
    is_Some (IT_to_V (f α)) → is_Some (IT_to_V α).
  Proof.
    destruct (IT_dont_confuse α)
      as [[e Ha] | [[n Ha] | [ [g Ha] | [[la Ha]|[op [i [k Ha]]]] ]]].
    - rewrite Ha hom_err. rewrite IT_to_V_Err. done.
    - rewrite Ha IT_to_V_Ret. done.
    - rewrite Ha IT_to_V_Fun. done.
    - rewrite Ha hom_tick. rewrite IT_to_V_Tau.
      intros []. exfalso. naive_solver.
    - rewrite Ha. rewrite hom_vis.
      rewrite IT_to_V_Vis. intros []. exfalso. naive_solver.
  Qed.

  #[export] Instance get_val_hom (f : IT -n> IT) : IT_hom (get_val f).
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. apply get_val_tick.
    - intros op' i k. apply get_val_vis.
    - intros e. apply get_val_err.
  Qed.
  #[export] Instance get_ret_hom (f : A -n> IT) : IT_hom (get_ret f).
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. apply get_ret_tick.
    - intros op' i k. apply get_ret_vis.
    - intros e. apply get_ret_err.
  Qed.
  #[export] Instance get_fun_hom f : IT_hom (get_fun f).
  Proof.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. apply get_fun_tick.
    - intros op' i k. apply get_fun_vis.
    - intros e. apply get_fun_err.
  Qed.


End it_hom.

#[global] Opaque Ret Fun Tau Err Vis Tick.
#[global] Opaque get_ret get_val get_fun.
