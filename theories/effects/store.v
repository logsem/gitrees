(** Higher-order store effect *)
From iris.algebra Require Import gmap excl auth gmap_view list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.
From gitrees Require Import prelude.
From gitrees Require Import gitree.
From gitrees.lib Require Import eq.
Require gitrees.lib.pairs.

Opaque laterO_map.

(** State and operations *)
Canonical Structure locO := leibnizO loc.

Fixpoint gen_fresh_slice {A} (σ : gmap locO A)
  (p : nat) (a : A) : list (locO * A) :=
  match p with
  | 0 => []
  | S p => (gen_fresh_slice σ p a) ++ [(Loc.fresh (dom σ) +ₗ p, a)]
  end.

Lemma gen_fresh_slice_fresh {A} (σ : gmap loc A) p a :
  Forall (λ x, fst x ∉ dom σ) (gen_fresh_slice σ p a).
Proof.
  induction p as [| ? IH].
  - done.
  - simpl; apply Forall_app; split; first done.
    apply Forall_singleton; simpl.
    apply (Loc.fresh_fresh (dom σ) p).
    lia.
Qed.

Lemma gen_fresh_slice_val {A} (σ : gmap loc A) p a x y :
  (x, y) ∈ gen_fresh_slice σ p a → y = a.
Proof.
  induction p as [| ? IH].
  - simpl; intros H; inversion H.
  - simpl; intros [H | H%elem_of_list_singleton]%elem_of_app;
      first by apply IH.
    by inversion H; subst.
Qed.

Lemma gen_fresh_slice_elem {A} (σ : gmap loc A) p a x :
  x ∈ (gen_fresh_slice σ p a).*1 → (x, a) ∈ gen_fresh_slice σ p a.
Proof.
  induction p as [| ? IH].
  - simpl; inversion 1.
  - simpl; intros H.
    rewrite fmap_app in H.
    apply elem_of_app in H.
    destruct H as [H | ->%elem_of_list_singleton].
    + by apply elem_of_app; left; apply IH.
    + by apply elem_of_app; right; simpl; apply elem_of_list_singleton.
Qed.

Lemma gen_fresh_slice_no_dup {A} (σ : gmap loc A) p a :
  NoDup (gen_fresh_slice σ p a).*1.
Proof.
  apply NoDup_fmap_fst.
  {
    intros x y1 y2 H G.
    apply gen_fresh_slice_val in H, G.
    rewrite H G //=.
  }
  induction p as [| ? IH]; first by apply NoDup_nil.
  simpl; apply NoDup_app.
  split; first done.
  split; last apply NoDup_singleton.
  intros x H ->%elem_of_list_singleton.
  assert (∀ i : nat, (Loc.fresh (dom σ) +ₗ (p + i)%nat, a) ∉ gen_fresh_slice σ p a) as J.
  {
    clear.
    induction p as [| ? IH].
    - set_solver.
    - simpl; intros i [H | H%elem_of_list_singleton]%elem_of_app.
      + rewrite -PeanoNat.Nat.add_succ_r in H.
        by apply (IH (S i)).
      + inversion H as [J]; subst.
        apply Z.add_reg_l in J.
        lia.
  }
  specialize (J 0).
  rewrite PeanoNat.Nat.add_0_r in J.
  apply (J H).
Qed.

Lemma gen_fresh_slice_fmap_L {A B} (σ : gmap loc A) p a
  (f : A → B)
  : (gen_fresh_slice (f <$> σ) p (f a))
    = (prod_map id f <$> gen_fresh_slice σ p a).
Proof.
  induction p as [| ? IH]; first done.
  rewrite /= IH.
  rewrite fmap_app.
  f_equal. rewrite list_fmap_singleton /=.
  rewrite dom_fmap_L.
  reflexivity.
Qed.

Global Instance gen_fresh_slice_ne {A : ofe} : NonExpansive3 (gen_fresh_slice (A := A)).
Proof.
  intros n x y H x' y' G a.
  revert y' G x y H a.
  induction x' as [| ? IH]; intros y' G x y H a b J.
  - rewrite -G /=.
    apply dist_equivalence.
  - rewrite -G /=.
    specialize (IH x' (reflexivity _) x y H a b J).
    apply gmap_dom_ne in H. rewrite H.
    f_equiv; last by f_equiv.
    apply IH.
Qed.

Global Instance list_to_map_ne {A : ofe}
  : NonExpansive (list_to_map (K := locO) (A := A) (M := gmap locO A)).
Proof.
  intros n x y H.
  revert y H.
  induction x as [| ? ? IH]; intros y H.
  - symmetry in H.
    apply nil_dist_eq in H.
    rewrite H.
    reflexivity.
  - symmetry in H.
    apply cons_dist_eq in H.
    destruct H as [a' [l' [H1 [H2 ->]]]].
    simpl.
    rewrite IH; last (symmetry; eassumption).
    destruct a as [a1 a2]; destruct a' as [a'1 a'2].
    destruct H1 as [G1 G2]; simpl in G1, G2. simpl.
    rewrite G1.
    by f_equiv.
Qed.

Definition stateF : oFunctor := (gmapOF locO (▶ ∙))%OF.

#[local] Instance state_inhabited X `{!Cofe X} : Inhabited (stateF ♯ X).
Proof. apply _. Qed.
#[local] Instance state_cofe X `{!Cofe X} : Cofe (stateF ♯ X).
Proof. apply _. Qed.

Definition state_read X `{!Cofe X} : loc * (stateF ♯ X) → option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '(l,σ), x ← σ !! l;
               Some (x, σ, []).
#[export] Instance state_read_ne X `{!Cofe X} :
  NonExpansive (state_read X : prodO locO (stateF ♯ X) → optionO ((laterO X) * (stateF ♯ X) * listO (laterO X)))%type.
Proof.
  intros n [l1 s1] [l2 s2]. simpl. intros [-> Hs].
  eapply option_mbind_ne; last done.
  solve_proper.
Qed.

Definition state_dealloc X `{!Cofe X} : loc * (stateF ♯ X) → option (unitO * (stateF ♯ X) * listO (laterO X))
  := λ '(l,σ), Some ((), delete l σ, []).
#[export] Instance state_dealloc_ne X `{!Cofe X} :
  NonExpansive (state_dealloc X : prodO locO (stateF ♯ X) → optionO (unitO * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [l1 s1] [l2 s2]. simpl. intros [-> Hs].
  solve_proper.
Qed.

Definition state_write X `{!Cofe X} :
  (loc * (laterO X)) * (stateF ♯ X) → option (unit * (stateF ♯ X) * listO (laterO X))
  := λ '((l,n),s), let s' := <[l:=n]>s
                   in Some ((), s', []).
#[export] Instance state_write_ne X `{!Cofe X} :
  NonExpansive (state_write X : prodO (prodO locO _) (stateF ♯ _) → optionO (unitO * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [[l1 m1] s1] [[l2 m2] s2]. simpl.
  intros [[Hl%leibnizO_leibniz Hm] Hs]. simpl in Hl.
  rewrite Hl. solve_proper.
Qed.

Definition state_allocN X `{!Cofe X} : (natO * (laterO X)) * (stateF ♯ X) → option (loc * (stateF ♯ X) * listO (laterO X))
  := λ '((m,n),s), let l := Loc.fresh (dom s) in
                   let s' : gmap locO (laterO X) := list_to_map (gen_fresh_slice s m n) in
                   let s'' := s' ∪ s in
                   Some (l, s'', []).
#[export] Instance state_allocN_ne X `{!Cofe X} :
  NonExpansive (state_allocN X : prodO _ (stateF ♯ X) → optionO (locO * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [[p1 m1] s1] [[p2 m2] s2]. simpl.
  intros [[Hp Hm] Hs]. simpl in *.
  set (l1 := Loc.fresh (dom s1)).
  set (l2 := Loc.fresh (dom s2)).
  assert (l1 = l2) as ->.
  { unfold l1,l2. f_equiv. eapply gmap_dom_ne, Hs. }
  do 3 f_equiv.
  f_equiv; last done.
  f_equiv.
  by f_equiv.
Qed.

Definition state_atomic X `{!Cofe X} :
  (loc
   * (laterO (X -n> (X * X)%type)))
  * (stateF ♯ X)
  -> option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '((l, h), σ),
    v ← σ !! l;
    let r := later_ap h v in
    Some (later_map fst r, <[l := later_map snd r]>σ, []).
#[export] Instance state_atomic_ne X `{!Cofe X} :
  NonExpansive (state_atomic X : prodO _ (stateF ♯ X)
                                 → optionO (laterO X
                                            * (stateF ♯ X)
                                            * listO (laterO X))%type).
Proof.
  intros n [[m1 k1] p1] [[m2 k2] p2]. simpl.
  intros [[Hm Hk] Hp]. simpl in *.
  f_equiv.
  - intros ?? Hxy; simpl.
    do 3 f_equiv.
    + rewrite !later_map_Next.
      apply Next_contractive.
      destruct n.
      * apply dist_later_0.
      * apply dist_later_S.
        do 2 f_equiv.
        -- apply Hk; lia.
        -- apply Hxy; lia.
    + rewrite !later_map_Next.
      rewrite Hm.
      f_equiv; last done.
      apply Next_contractive.
      destruct n.
      -- apply dist_later_0.
      -- apply dist_later_S.
         do 2 f_equiv.
         ++ apply Hk; lia.
         ++ apply Hxy; lia.
  - by rewrite Hp Hm.
Qed.

Program Definition ReadE : opInterp :=  {|
  Ins := locO;
  Outs := (▶ ∙);
|}.
Program Definition WriteE : opInterp :=  {|
  Ins := (locO * (▶ ∙))%OF;
  Outs := unitO;
|}.
Program Definition AllocE : opInterp :=  {|
  Ins := (natO * (▶ ∙))%OF;
  Outs := locO;
|}.
Program Definition DeallocE : opInterp :=  {|
  Ins := locO;
  Outs := unitO;
|}.
Program Definition AtomicE : opInterp := {|
  Ins := (locO * ▶ (∙ -n> (∙ * ∙)))%OF;
  Outs := (▶ ∙);
|}.

Definition storeE : opsInterp := @[ReadE;WriteE;AllocE;DeallocE;AtomicE].
Canonical Structure reify_store : sReifier NotCtxDep.
Proof.
  simple refine {| sReifier_ops := storeE |}.
  intros X HX op.
  destruct op as [[]|[[]|[[]|[|[|[]]]]]]; simpl.
  - simple refine (OfeMor (state_read X)).
  - simple refine (OfeMor (state_write X)).
  - simple refine (OfeMor (state_allocN X)).
  - simple refine (OfeMor (state_dealloc X)).
  - simple refine (OfeMor (state_atomic X)).
Defined.

Section simple_constructors.
  Context {E : opsInterp}.
  Context `{!subEff storeE E}.
  Context {R} `{!Cofe R}.
  Context `{!SubOfe unitO R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Program Definition ALLOC_N : natO -n> IT -n> (locO -n> IT) -n> IT :=
    (λne p n k, Vis (E:=E) (subEff_opid $ inr (inr (inl ())))
      (subEff_ins (F:=storeE) (op:=inr (inr (inl ()))) (p, Next n))
      (NextO ◎ k ◎ (subEff_outs (F:=storeE) (op:=inr (inr (inl ()))))^-1)).
  Solve Obligations with solve_proper.

  Program Definition ALLOC : IT -n> (locO -n> IT) -n> IT := ALLOC_N 1.

  Program Definition READ : locO -n> IT :=
    λne l, Vis (E := E) (subEff_opid $ inl ())
                (subEff_ins (F := storeE) (op:=(inl ())) l)
                ((subEff_outs (F := storeE) (op:=(inl ())))^-1).

  Program Definition WRITE : locO -n> IT -n> IT :=
    λne l a, Vis (E := E) (subEff_opid $ inr (inl ()))
                (subEff_ins (F := storeE) (op := (inr $ inl ())) (l, (Next a)))
                (λne _, Next (Ret ())).
  Solve Obligations with solve_proper.

  Program Definition DEALLOC : locO -n> IT :=
    λne l, Vis (E := E) (subEff_opid $ inr $ inr $ inr $ inl ())
                (subEff_ins (F := storeE) (op := (inr $ inr $ inr $ inl ())) l)
                (λne _, Next (Ret ())).

  Program Definition ATOMIC : locO -n> (IT -n> (prodO IT IT)) -n> IT :=
    λne l f,
      Vis (E := E) (subEff_opid $ inr $ inr $ inr $ inr $ inl ())
        (subEff_ins (F := storeE) (op := (inr $ inr $ inr $ inr $ inl ()))
           (l, (Next f)))
        (ofe_iso_2 (subEff_outs (F := storeE) (op := (inr $ inr $ inr $ inr $ inl ())))).
  Solve All Obligations with solve_proper.

End simple_constructors.

Module cas.
  Export IF_bool.
  Export gitrees.lib.pairs.
  Section cas.
    Context {E : opsInterp}.
    Context `{!subEff storeE E}.
    Context {R} `{!Cofe R}.
    Context `{!SubOfe boolO R} `{!Ofe_decide_eq R}.
    Notation IT := (IT E R).
    Notation ITV := (ITV E R).

    Program Definition cas_compute
      : IT -n> IT -n> IT -n> (IT * IT)%type :=
      λne w1 w2 v, ((pairIT v (safe_compare (A := R) (E := E) w1 v))
                     , IF (safe_compare (A := R) (E := E) w1 v) w2 v).
    Solve All Obligations with solve_proper_please.

    Program Definition CAS
      : locO -n> IT -n> IT -n> IT := λne l w1 w2, ATOMIC l (cas_compute w1 w2).
    Solve All Obligations with solve_proper_please.
  End cas.
End cas.

Module xchg.
  Section xchg.
    Context {E : opsInterp}.
    Context `{!subEff storeE E}.
    Context {R} `{!Cofe R}.
    Notation IT := (IT E R).
    Notation ITV := (ITV E R).

    Program Definition xchg_compute
      : IT -n> IT -n> (IT * IT)%type :=
      λne w v, (v, w).
    Solve All Obligations with solve_proper.

    Program Definition XCHG
      : locO -n> IT -n> IT :=
      λne l w, ATOMIC l (xchg_compute w).
    Solve All Obligations with solve_proper_please.
  End xchg.
End xchg.

Module faa.
  Section faa.
    Context {E : opsInterp}.
    Context `{!subEff storeE E}.
    Context {R} `{!Cofe R}.
    Context `{SubOfe A R}.
    Notation IT := (IT E R).
    Notation ITV := (ITV E R).

    Program Definition faa_compute (f : A -n> A -n> A)
      : IT -n> IT -n> (IT * IT)%type :=
      λne w v, (v, get_ret2 (λne x y, Ret (f x y)) w v).
    Solve All Obligations with solve_proper_please.

    Program Definition FAA (f : A -n> A -n> A)
      : locO -n> IT -n> IT :=
      λne l w, ATOMIC l (faa_compute f w).
    Solve All Obligations with solve_proper_please.
  End faa.
End faa.

Section wp.
  Context {n : nat}.
  Context {a : is_ctx_dep}.
  Variable (rs : gReifiers a n).
  Context {R} {CR : Cofe R}.
  Context {SO : SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).

  (* a separate ghost state for keeping track of locations *)
  Definition istate := gmap_viewR loc (agreeR (laterO IT)).
  Class heapPreG Σ := HeapPreG { heapPreG_inG :: inG Σ istate }.
  Class heapG Σ := HeapG {
      heapG_inG :: inG Σ istate;
      heapG_name : gname;
    }.
  Definition heapΣ : gFunctors := GFunctor istate.
  #[export] Instance subG_heapΣ {Σ} : subG heapΣ Σ → heapPreG Σ.
  Proof. solve_inG. Qed.

  Lemma new_heapG σ `{!heapPreG Σ} :
    (⊢ |==> ∃ `{!heapG Σ}, own heapG_name (●V σ): iProp Σ)%I.
  Proof.
    iMod (own_alloc (●V σ)) as (γ) "H".
    { apply gmap_view_auth_valid. }
    pose (sg := {| heapG_inG := _; heapG_name := γ |}).
    iModIntro. iExists sg. by iFrame.
  Qed.

  Context `{!subReifier (sReifier_NotCtxDep_min reify_store a) rs}.
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  (** * The ghost state theory for the heap *)

  Context `{!heapG Σ}.

  Program Definition heap_ctx :=
    inv (nroot.@"storeE")
      (∃ σ, £ 1 ∗ has_substate σ ∗ own heapG_name (●V (fmap (M := gmap locO) to_agree σ)))%I.

  Program Definition pointsto (l : loc) (α : IT) : iProp :=
    own heapG_name $ gmap_view_frag l (DfracOwn 1) (to_agree (Next α)).
  Global Instance pointsto_proper l : Proper ((≡) ==> (≡)) (pointsto l).
  Proof. solve_proper. Qed.
  Global Instance pointsto_ne l : NonExpansive (pointsto l).
  Proof. solve_proper. Qed.

  Lemma istate_alloc α l σ :
    σ !! l = None →
    own heapG_name (●V σ) ==∗ own heapG_name (●V (<[l:=to_agree (Next α)]>σ))
                   ∗ pointsto l α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { by apply (gmap_view_alloc _ l (DfracOwn 1) (to_agree (Next α))); eauto. }
    done.
  Qed.

  Lemma istate_allocN α (p : nat) (σ : gmap loc (agreeR (laterO IT))) :
    own heapG_name (●V σ)
    ==∗ own heapG_name (●V ((list_to_map (gen_fresh_slice σ p (to_agree (Next α)))) ∪ σ))
      ∗ ([∗ list] k ∈ seqZ 0 p, pointsto (Loc.fresh (dom σ) +ₗ k) α).
  Proof.
    iIntros "H".
    iMod (own_update with "H") as "[H1 H2]".
    {
      apply (gmap_view_alloc_big σ
               (list_to_map (gen_fresh_slice σ p (to_agree (Next α))))
               (DfracOwn 1)); last done.
      apply map_disjoint_dom_2.
      apply elem_of_disjoint.
      intros x H G.
      pose proof (gen_fresh_slice_fresh σ p (to_agree (Next α))) as J.
      rewrite Forall_forall in J.
      specialize (J (x, (to_agree (Next α)))).
      apply J; last done.
      clear -H.
      apply dom_list_to_map in H.
      apply elem_of_list_to_set in H.
      by apply gen_fresh_slice_elem.
    }
    rewrite /gmap_view_auth.
    iFrame "H1".
    rewrite /pointsto.
    rewrite big_opM_own_1.
    rewrite big_sepM_list_to_map; last apply gen_fresh_slice_no_dup.
    iInduction p as [| p] "IH"; first done.
    rewrite seqZ_S.
    rewrite /= big_sepL_app big_sepL_app /=.
    rewrite Z.add_0_l.
    iDestruct "H2" as "(H2 & H3 & H4)".
    iFrame "H4".
    iMod ("IH" with "H2") as "H2".
    iFrame "H2".
    iModIntro.
    iFrame "H3".
  Qed.

  Lemma istate_read l α σ :
    own heapG_name (●V (fmap (M := gmap locO) to_agree σ)) -∗ pointsto l α
    -∗ (σ !! l) ≡ Some (Next α).
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[%H Hval]".
    rewrite lookup_fmap.
    rewrite option_equivI.
    destruct (σ !! l) as [o |] eqn:Heq.
    - rewrite Heq /=.
      rewrite agree_equivI.
      by iRewrite "Hval".
    - rewrite Heq /=.
      done.
  Qed.
  Lemma istate_loc_dom l α σ :
    own heapG_name (●V (fmap (M := gmap locO) to_agree σ)) -∗ pointsto l α -∗ ⌜is_Some (σ !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (istate_read with "Hinv Hloc") as "Hl".
    destruct (σ !! l) ; eauto.
    by rewrite option_equivI.
  Qed.

  Lemma istate_write l α β σ :
    own heapG_name (●V σ) -∗ pointsto l α ==∗ own heapG_name (●V <[l:=(to_agree (Next β))]>σ)
                                  ∗ pointsto l β.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]"; last done.
    apply gmap_view_update.
  Qed.

  Lemma istate_delete l α σ :
    own heapG_name (●V σ) -∗ pointsto l α ==∗ own heapG_name (●V delete l σ).
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "$".
    { apply (gmap_view_delete). }
    done.
  Qed.

  (** * The symbolic execution rules *)
  Lemma wp_read_atomic_hom (l : loc)  E1 E2 s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (pointsto l α ={E2,E1}=∗ WP@{rs} (κ α) @ s {{ Φ }})) -∗
    WP@{rs} κ (READ l) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    unfold READ. simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken E1).
    { set_solver. }
    iIntros "Hwk".
    iMod "H" as (α) "[Hp Hback]".
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iAssert (⌜is_Some (σ !! l)⌝)%I as "%Hdom".
    { iApply (istate_loc_dom with "Hh Hp"). }
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [β' Hb'].
    iAssert ((σ !! l ≡ Some (Next α)))%I as "#Hlookup".
    { iApply (istate_read with "Hh Hp"). }
    iAssert (▷ (β' ≡ α))%I as "#Hba".
    { rewrite Hx. rewrite option_equivI.
      rewrite Hb'. by iNext. }
    iClear "Hlookup".
    iExists σ,(Next β'),σ,(κ β'), [].
    iFrame "Hs".
    repeat iSplit.
    - by rewrite /= Hx /= Hb'.
    - iPureIntro. by rewrite /= ofe_iso_21 laterO_map_Next.
    - iNext. iIntros "Hlc Hs".
      iMod ("Hback" with "Hp") as "Hback".
      iMod "Hwk" .
      iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
      { iExists _. by iFrame. }
      iRewrite "Hba".
      iModIntro; iSplit; done.
  Qed.

  Lemma wp_read_atomic (l : loc)  E1 E2 s Φ :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx
    -∗ (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
                          ▷ ▷ (pointsto l α ={E2,E1}=∗ WP@{rs} α @ s {{ Φ }}))
    -∗ WP@{rs} (READ l) @ s {{ Φ }}.
  Proof.
    iIntros "%Hm H".
    iApply (wp_read_atomic_hom l E1 E2 s Φ idfun Hm with "H").
  Qed.

  Lemma wp_read_hom (l : loc) (α : IT) s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ (pointsto l α -∗ WP@{rs} κ α @ s {{ Φ }}) -∗
    WP@{rs} κ (READ l) @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    iApply (wp_read_atomic_hom _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext. iIntros "Hl".
    iModIntro. by iApply "Ha".
  Qed.

  Lemma wp_read (l : loc) (α : IT) s Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ (pointsto l α -∗ WP@{rs} α @ s {{ Φ }}) -∗
    WP@{rs} READ l @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    iApply (wp_read_hom _ _ _ _ idfun with "Hcxt Hp Ha").
  Qed.

  Lemma wp_write_atomic_hom (l : loc)  E1 E2 β s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (pointsto l β ={E2,E1}=∗ WP@{rs} κ (Ret ()) @ s {{ β, Φ β }})) -∗
    WP@{rs} κ (WRITE l β) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    unfold WRITE; rewrite /= hom_vis.
    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken E1).
    { set_solver. }
    iIntros "Hwk".
    iMod "H" as (α) "[Hp Hback]".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hp"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iExists σ,(),(<[l:=Next β]>σ),(κ (Ret ())), [].
    iFrame "Hs".
    iSimpl. repeat iSplit; [ done | done | ].
    iNext. iIntros "Hlc".
    iMod (istate_write _ _ β with "Hh Hp") as "[Hh Hp]".
    iIntros "Hs".
    iMod ("Hback" with "Hp") as "Hback".
    iMod "Hwk" .
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. rewrite -(fmap_insert to_agree σ). by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma wp_write_atomic (l : loc)  E1 E2 β s Φ :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx
    -∗ (|={E1,E2}=> ∃ α, ▷ pointsto l α
                        ∗ ▷ ▷ (pointsto l β ={E2,E1}=∗ Φ (RetV ())))
    -∗ WP@{rs} WRITE l β @ s {{ Φ }}.
  Proof.
    iIntros "%Hm H G".
    iApply (wp_write_atomic_hom l E1 E2 _ _ _ idfun Hm with "H [G]").
    iMod "G".
    iModIntro.
    iDestruct "G" as "(%α & G1 & G2)".
    iExists α; iFrame "G1".
    do 2 iNext.
    iIntros "H".
    iMod ("G2" with "H") as "G".
    iModIntro.
    iApply wp_val.
    by iModIntro.
  Qed.

  Lemma wp_write_hom (l : loc) (α β : IT) s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷▷ (pointsto l β -∗ WP@{rs} κ (Ret ()) @ s {{ β, Φ β }}) -∗
    WP@{rs} κ (WRITE l β) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply (wp_write_atomic_hom _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext. iIntros "Hl".
    iModIntro. by iApply "Ha".
  Qed.

  Lemma wp_write (l : loc) (α β : IT) s Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷▷ (pointsto l β -∗ Φ (RetV ())) -∗
    WP@{rs} WRITE l β @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply (wp_write_hom _ _ _ _ _ idfun with "Hctx Hp [Ha]").
    do 2 iNext.
    iIntros "H".
    iDestruct ("Ha" with "H") as "G".
    iApply wp_val.
    by iModIntro.
  Qed.

  Lemma wp_alloc_hom (α : IT) (k : locO -n> IT) s Φ `{!NonExpansive Φ}
    (κ : IT -n> IT) `{!IT_hom κ} :
    heap_ctx -∗
    ▷▷ (∀ l, pointsto l α -∗ WP@{rs} κ (k l) @ s {{ Φ }}) -∗
    WP@{rs} κ (ALLOC α k) @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    set (l:=Loc.fresh (dom σ)).
    iExists σ,l,_,(κ (k l)), [].
    iFrame "Hs".
    simpl. change (Loc.fresh (dom σ)) with l.
    iSplit; first done.
    iSplit.
    { simpl. rewrite ofe_iso_21. done. }
    iNext. iIntros "Hlc Hs".
    iMod (istate_alloc α l with "Hh") as "[Hh Hl]".
    {
      apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite dom_fmap_L.
      rewrite -(Loc.add_0 l).
      apply Loc.fresh_fresh. lia.
    }
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    {
      iExists _.
      rewrite -(fmap_insert to_agree σ).
      rewrite Loc.add_0.
      rewrite insert_empty -insert_union_singleton_l.
      by iFrame.
    }
    rewrite /weakestpre.wptp big_sepL2_nil.
    by iDestruct ("H" with "Hl") as "$".
  Qed.

  Lemma wp_alloc_n_hom (p : nat) (α : IT) (k : locO -n> IT) s Φ `{!NonExpansive Φ}
    (κ : IT -n> IT) `{!IT_hom κ} :
    heap_ctx -∗
    ▷▷ (∀ l, ([∗ list] k ∈ seqZ 0 p, pointsto (l +ₗ k) α) -∗ WP@{rs} κ (k l) @ s {{ Φ }}) -∗
    WP@{rs} κ (ALLOC_N p α k) @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    set (l:=Loc.fresh (dom σ)).
    iExists σ,l,_,(κ (k l)), [].
    iFrame "Hs".
    simpl. change (Loc.fresh (dom σ)) with l.
    iSplit; first done.
    iSplit.
    { simpl. rewrite ofe_iso_21. done. }
    iNext. iIntros "Hlc Hs".
    iMod (istate_allocN α p with "Hh") as "[Hh Hl]".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    {
      iExists _. iNext.
      iFrame "Hs Hlc".
      rewrite map_fmap_union.
      rewrite -list_to_map_fmap.
      rewrite gen_fresh_slice_fmap_L.
      by iFrame.
    }
    rewrite /weakestpre.wptp big_sepL2_nil.
    rewrite dom_fmap_L.
    by iDestruct ("H" with "Hl") as "$".
  Qed.

  Lemma wp_alloc (α : IT) (k : locO -n> IT) s Φ `{!NonExpansive Φ} :
    heap_ctx -∗
    ▷▷ (∀ l, pointsto l α -∗ WP@{rs} k l @ s {{ Φ }}) -∗
    WP@{rs} ALLOC α k @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    iApply (wp_alloc_hom _ _ _ _ idfun with "Hh H").
  Qed.

  Lemma wp_alloc_n (p : nat) (α : IT) (k : locO -n> IT) s Φ `{!NonExpansive Φ} :
    heap_ctx -∗
    ▷▷ (∀ l, ([∗ list] k ∈ seqZ 0 p, pointsto (l +ₗ k) α) -∗ WP@{rs} k l @ s {{ Φ }}) -∗
    WP@{rs} ALLOC_N p α k @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    iApply (wp_alloc_n_hom p _ _ _ _ idfun with "Hh H").
  Qed.

  Lemma wp_dealloc_atomic_hom (l : loc)  E1 E2 s Φ
    (κ : IT -n> IT) `{!IT_hom κ} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (|={E2,E1}=> WP@{rs} κ (Ret ()) @ s {{ β, Φ β }})) -∗
    WP@{rs} κ (DEALLOC l) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''. simpl.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken E1).
    { set_solver. }
    iIntros "Hwk".
    iMod "H" as (α) "[Hp Hback]".
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iAssert (⌜is_Some (σ !! l)⌝)%I as "%Hdom".
    { iApply (istate_loc_dom with "Hh Hp"). }
    destruct Hdom as [x Hx].
    iExists σ,(),(delete l σ),(κ (Ret ())), [].
    iFrame "Hs".
    repeat iSplit; simpl; eauto.
    iNext. iIntros "Hlc Hs".
    iMod (istate_delete with "Hh Hp") as "Hh".
    iMod ("Hback") as "Hback".
    iMod "Hwk" .
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    {
      iExists _.
      rewrite -(fmap_delete to_agree σ).
      by iFrame.
    }
    iModIntro; by iFrame.
  Qed.

  Lemma wp_dealloc_atomic (l : loc)  E1 E2 s Φ :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (|={E2,E1}=> Φ (RetV ()))) -∗
    WP@{rs} DEALLOC l @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    iApply (wp_dealloc_atomic_hom _ _ _ _ _ idfun with "Hcxt [H]");
      first done.
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%α & G1 & G2)".
    iExists α; iFrame "G1".
    do 2 iNext.
    iMod "G2".
    iModIntro.
    iApply wp_val.
    by iModIntro.
  Qed.

  Lemma wp_dealloc_hom (l : loc) α s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ WP@{rs} κ (Ret ()) @ s {{ β, Φ β }} -∗
    WP@{rs} κ (DEALLOC l) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hl H".
    iApply (wp_dealloc_atomic_hom _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext.
    iModIntro. done.
  Qed.

  Lemma wp_dealloc (l : loc) α s Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ Φ (RetV ()) -∗
    WP@{rs} DEALLOC l @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hl H".
    iApply (wp_dealloc_hom _ _ _ _ idfun with "Hctx Hl [H]").
    do 2 iNext.
    iApply wp_val.
    iModIntro. done.
  Qed.

  Lemma wp_atomic_atomic_hom
    (f : IT -n> prodO IT IT)
    (l : loc) w1 w2 E1 E2 s Φ (κ : IT -n> IT) `{!IT_hom κ} :
      nclose (nroot.@"storeE") ## E1 →
      heap_ctx
      -∗ (|={E1,E2}=> ∃ α, ▷ pointsto l α
                           ∗ ▷ (f α ≡ (w1, w2))
                           ∗ ▷ ▷ (pointsto l w2
                                  ={E2,E1}=∗ WP@{rs} (κ w1) @ s {{ Φ }}))
      -∗ WP@{rs} κ (ATOMIC l f) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    unfold ATOMIC; simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken E1).
    { set_solver. }
    iIntros "Hwk".
    iMod "H" as (α) "[Hp [#Hcond Hback]]".
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iAssert (⌜is_Some (σ !! l)⌝)%I as "%Hdom".
    { iApply (istate_loc_dom with "Hh Hp"). }
    destruct Hdom as [x Hx].
    iAssert ((σ !! l ≡ Some (Next α)))%I as "#Hlookup".
    { iApply (istate_read with "Hh Hp"). }
    destruct (Next_uninj x) as [β' Hb'].
    assert (σ !! l ≡ Some (Next β')) as Hx'.
    { by rewrite Hx Hb'. }
    iExists σ, (Next w1), (<[l:=Next w2]>σ), (κ w1), [].
    iFrame "Hs".
    repeat iSplit.
    - rewrite /=.
      match goal with
      | |- context G [_ ≫= ?F] =>
          set (F' := F)
      end.
      iApply (internal_eq_rewrite _ _
                (λ x : option (later IT),
                    (x ≫= F' ≡ Some (Next w1, (<[l:=Next w2]>σ), []))%I)
               with "[Hlookup]").
      {
        intros m ?? G.
        f_equiv.
        apply option_mbind_ne.
        - subst F'.
          intros ?? H.
          solve_proper_prepare.
          do 3 f_equiv.
          + f_equiv.
            apply Next_contractive.
            destruct m.
            * apply dist_later_0.
            * apply dist_later_S.
              f_equiv.
              apply H; lia.
          + do 2 f_equiv.
            apply Next_contractive.
            destruct m.
            * apply dist_later_0.
            * apply dist_later_S.
              f_equiv.
              apply H; lia.
        - done.
      }
      {
        iApply internal_eq_sym.
        rewrite Hx'.
        iApply "Hlookup".
      }
      {
        subst F'.
        rewrite /=.
        iRewrite "Hcond".
        rewrite !later_map_Next /=.
        done.
      }
    - iPureIntro. by rewrite /= ofe_iso_21 laterO_map_Next.
    - iNext. iIntros "Hlc Hs".
      iMod (istate_write l α w2 with "Hh Hp") as "[Hh Hp]".
      iMod ("Hback" with "Hp") as "Hback".
      iMod "Hwk" .
      iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
      { iExists _. rewrite -(fmap_insert to_agree σ). by iFrame. }
      iModIntro.
      iSplit; last done.
      iApply "Hback".
  Qed.

  Lemma wp_atomic_hom (f : IT -n> prodO IT IT)
    (l : loc) α w1 w2 s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    heap_ctx
    -∗ ▷ pointsto l α
    -∗ ▷ (f α ≡ (w1, w2))
    -∗ ▷▷ (pointsto l w2 -∗ WP@{rs} (κ w1) @ s {{ β, Φ β }})
    -∗ WP@{rs} κ (ATOMIC l f) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hl HEQ H".
    iApply (wp_atomic_atomic_hom _ l _ _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext.
    iIntros "G".
    iModIntro.
    by iApply "H".
  Qed.
End wp.

Arguments heapG {_} {_} rs R {_} Σ.
Arguments heapPreG {_} {_} rs R {_} Σ.
Arguments heapΣ {_} {_} rs R {_}.
Arguments heap_ctx {_ _} rs {_ _ _ _ _ _}.
Arguments pointsto {_ _ _ _ _ _ _} _ _.
#[global]  Opaque ALLOC READ WRITE DEALLOC ATOMIC.

Module cas_wp.
  Export cas.
  Section wp.
    Context {n : nat}.
    Context {a : is_ctx_dep}.
    Variable (rs : gReifiers a n).
    Context {R} {CR : Cofe R}.
    Context `{!SubOfe unitO R}.
    Context `{!SubOfe boolO R}.
    Context `{!Ofe_decide_eq R}.
    Notation F := (gReifiers_ops rs).
    Notation IT := (IT F R).
    Notation ITV := (ITV F R).
    Notation stateO := (stateF ♯ IT).
    Context `{!subReifier (sReifier_NotCtxDep_min reify_store a) rs}.
    Context `{!gitreeGS_gen rs R Σ}.
    Notation iProp := (iProp Σ).
    Context `{!heapG rs R Σ}.

    Lemma wp_cas_fail_hom (l : loc) α w1 w2 s Φ
      (κ : IT -n> IT) `{!IT_hom κ} :
      heap_ctx rs
      -∗ ▷ pointsto l α
      -∗ ▷ (safe_compare w1 α ≡ Ret false)
      -∗ ▷ ▷ (pointsto l α -∗ WP@{rs} (κ (pairIT α (Ret false))) @ s {{ Φ }})
      -∗ WP@{rs} κ (CAS l w1 w2) @ s {{ Φ }}.
    Proof.
      iIntros "#Hcxt H HEQ G".
      unfold CAS.
      iApply (wp_atomic_hom with "Hcxt H [HEQ] G").
      iNext; simpl.
      iRewrite "HEQ".
      rewrite IF_False.
      rewrite !get_val_ret /=.
      done.
    Qed.

    Lemma wp_cas_succ_hom (l : loc) α w1 w2 s Φ
      (κ : IT -n> IT) `{!IT_hom κ} :
      heap_ctx rs
      -∗ ▷ pointsto l α
      -∗ ▷ (safe_compare w1 α ≡ Ret true)
      -∗ ▷ ▷ (pointsto l w2 -∗ WP@{rs} (κ (pairIT α (Ret true))) @ s {{ Φ }})
      -∗ WP@{rs} κ (CAS l w1 w2) @ s {{ Φ }}.
    Proof.
      iIntros "#Hcxt H HEQ G".
      unfold CAS.
      iApply (wp_atomic_hom with "Hcxt H [HEQ] G").
      iNext; simpl.
      iRewrite "HEQ".
      rewrite IF_True.
      rewrite !get_val_ret /=.
      done.
    Qed.
  End wp.
  #[global] Opaque CAS.
End cas_wp.

Module xchg_wp.
  Export xchg.
  Section wp.
    Context {n : nat}.
    Context {a : is_ctx_dep}.
    Variable (rs : gReifiers a n).
    Context {R} {CR : Cofe R}.
    Context `{!SubOfe unitO R}.
    Notation F := (gReifiers_ops rs).
    Notation IT := (IT F R).
    Notation ITV := (ITV F R).
    Notation stateO := (stateF ♯ IT).
    Context `{!subReifier (sReifier_NotCtxDep_min reify_store a) rs}.
    Context `{!gitreeGS_gen rs R Σ}.
    Notation iProp := (iProp Σ).
    Context `{!heapG rs R Σ}.

    Lemma wp_xchg_hom (l : loc) α w s Φ
      (κ : IT -n> IT) `{!IT_hom κ} :
      heap_ctx rs
      -∗ ▷ pointsto l α
      -∗ ▷ ▷ (pointsto l w -∗ WP@{rs} (κ α) @ s {{ Φ }})
      -∗ WP@{rs} κ (XCHG l w) @ s {{ Φ }}.
    Proof.
      iIntros "#Hcxt H G".
      unfold XCHG.
      iApply (wp_atomic_hom with "Hcxt H [] G").
      iNext; simpl.
      done.
    Qed.
  End wp.
  #[global] Opaque XCHG.
End xchg_wp.

Module faa_wp.
  Export faa.
  Section wp.
    Context {n : nat}.
    Context {a : is_ctx_dep}.
    Variable (rs : gReifiers a n).
    Context {R} {CR : Cofe R}.
    Context `{!SubOfe A R}.
    Notation F := (gReifiers_ops rs).
    Notation IT := (IT F R).
    Notation ITV := (ITV F R).
    Notation stateO := (stateF ♯ IT).
    Context `{!subReifier (sReifier_NotCtxDep_min reify_store a) rs}.
    Context `{!gitreeGS_gen rs R Σ}.
    Notation iProp := (iProp Σ).
    Context `{!heapG rs R Σ}.

    Lemma wp_faa_hom (f : A -n> A -n> A) (l : loc) α (w : A) s Φ
      (κ : IT -n> IT) `{!IT_hom κ} :
      heap_ctx rs
      -∗ ▷ pointsto l (Ret α)
      -∗ ▷ ▷ (pointsto l (Ret (f w α)) -∗ WP@{rs} (κ (Ret α)) @ s {{ Φ }})
      -∗ WP@{rs} κ (FAA f l (Ret w)) @ s {{ Φ }}.
    Proof.
      iIntros "#Hcxt H G".
      unfold FAA.
      iApply (wp_atomic_hom with "Hcxt H [] G").
      iNext; simpl.
      rewrite get_ret_ret /= get_ret_ret /=.
      done.
    Qed.
  End wp.
  #[global] Opaque FAA.
End faa_wp.
