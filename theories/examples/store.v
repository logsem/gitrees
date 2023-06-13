From Equations Require Import Equations.
From iris.algebra Require Import gmap excl auth gmap_view.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.
From gitrees Require Import prelude.
From gitrees Require Import gitree.

Opaque laterO_map.

(** State and operations *)
Canonical Structure locO := leibnizO loc.
Definition stateF : oFunctor := (gmapOF locO (▶ ∙))%OF.

#[local] Instance state_inhabited : Inhabited (stateF ♯ unitO).
Proof. apply _. Qed.
#[local] Instance state_cofe X `{!Cofe X} : Cofe (stateF ♯ X).
Proof. apply _. Qed.

Definition state_read X `{!Cofe X} : loc * (stateF ♯ X) → option (laterO X * (stateF ♯ X))
  := λ '(l,σ), x ← σ !! l;
               Some (x, σ).
#[export] Instance state_read_ne X `{!Cofe X} :
  NonExpansive (state_read X : prodO locO (stateF ♯ X) → optionO (prodO (laterO X) (stateF ♯ X))).
Proof.
  intros n [l1 s1] [l2 s2]. simpl. intros [-> Hs].
  apply (option_mbind_ne _ (λ n, Some (n, s1)) (λ n, Some (n, s2)));
    solve_proper.
Qed.

Definition state_write X `{!Cofe X} :
  (loc * (laterO X)) * (stateF ♯ X) → option (unit * (stateF ♯ X))
  := λ '((l,n),s), let s' := <[l:=n]>s
                   in Some ((), s').
#[export] Instance state_write_ne X `{!Cofe X} :
  NonExpansive (state_write X : prodO (prodO locO _) (stateF ♯ _) → optionO (prodO unitO (stateF ♯ X))).
Proof.
  intros n [[l1 m1] s1] [[l2 m2] s2]. simpl.
  intros [[Hl%leibnizO_leibniz Hm] Hs]. simpl in Hl.
  rewrite Hl. solve_proper.
Qed.

Definition state_alloc X `{!Cofe X} : (laterO X) * (stateF ♯ X) → option (loc * (stateF ♯ X))
  := λ '(n,s), let l := Loc.fresh (dom s) in
               let s' := <[l:=n]>s in
               Some (l, s').
#[export] Instance state_alloc_ne X `{!Cofe X} :
  NonExpansive (state_alloc X : prodO _ (stateF ♯ X) → optionO (prodO locO (stateF ♯ X))).
Proof.
  intros n [m1 s1] [m2 s2]. simpl.
  intros [Hm Hs]. simpl in *.
  set (l1 := Loc.fresh (dom s1)).
  set (l2 := Loc.fresh (dom s2)).
  assert (l1 = l2) as ->.
  { unfold l1,l2. f_equiv. eapply gmap_dom_ne, Hs. }
  solve_proper.
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
  Ins := (▶ ∙);
  Outs := locO;
|}.

Definition storeE : opsInterp := @[ReadE;WriteE;AllocE].
Canonical Structure reify_store : sReifier.
Proof.
  simple refine {| sReifier_ops := storeE |}.
  intros X HX op.
  destruct op as [[]|[[]|[[]|[]]]]; simpl.
  - simple refine (OfeMor (state_read X)).
  - simple refine (OfeMor (state_write X)).
  - simple refine (OfeMor (state_alloc X)).
Defined.

Section constructors.
  Context {E : opsInterp}.
  Context `{!subEff storeE E}.
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Program Definition ALLOC : IT -n> (locO -n> IT) -n> IT :=
    (λne n k, Vis (E:=E) (subEff_opid $ inr (inr (inl ())))
      (subEff_conv_ins (F:=storeE) (op:=inr (inr (inl ()))) (Next n))
      (NextO ◎ k ◎ subEff_conv_outs2 (F:=storeE) (op:=inr (inr (inl ()))))).
  Solve Obligations with solve_proper.

  Definition READ : locO -n> IT :=
    λne l, Vis (E:=E) (subEff_opid $ inl ())
                (subEff_conv_ins (F:=storeE) (op:=(inl ())) l)
                (subEff_conv_outs2 (F:=storeE) (op:=(inl ()))).


  Program Definition WRITE : locO -n> IT -n> IT :=
    λne l a, Vis (E:=E) (subEff_opid $ inr (inl ()))
                (subEff_conv_ins (F:=storeE) (op:=(inr $ inl ())) (l,(Next a)))
                (λne _, Next (Nat 0)).
  Solve Obligations with solve_proper.


End constructors.

Section wp.
  Context {n : nat}.
  Variable (rs : gReifiers n).
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).
  Notation stateO := (stateF ♯ IT).

  Context `{!subReifier reify_store rs}.
  Context `{!invGS_gen hlc Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  (** * The ghost state theory for the heap *)
  (* a separate ghost state for keeping track of locations *)
  Definition istate := gmap_viewUR loc (laterO IT).
  Class heapG Σ := HeapG {
      heapG_inG :: inG Σ istate;
      heapG_name : gname;
    }.
  Context `{!heapG Σ}.

  Definition heap_ctx := inv (nroot.@"storeE") (∃ σ, has_substate σ ∗ own heapG_name (●V σ))%I.
  Definition pointsto (l : loc) (α : IT) : iProp :=
    own heapG_name $ gmap_view_frag l (DfracOwn 1) (Next α).

  Lemma istate_alloc α l σ :
    σ !! l = None →
    own heapG_name (●V σ) ==∗ own heapG_name (●V (<[l:=(Next α)]>σ))
                   ∗ pointsto l α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { apply (gmap_view_alloc _ l (DfracOwn 1) (Next α)); eauto.
      done. }
    done.
  Qed.
  Lemma istate_read l α σ :
    own heapG_name (●V σ) -∗ pointsto l α -∗ σ !! l ≡ Some (Next α).
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[_ Hval]". done.
  Qed.
  Lemma istate_loc_dom l α σ :
    own heapG_name (●V σ) -∗ pointsto l α -∗ ⌜is_Some (σ !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (istate_read with "Hinv Hloc") as "Hl".
    destruct (σ !! l) ; eauto.
    by rewrite option_equivI.
  Qed.
  Lemma istate_write l α β σ :
    own heapG_name (●V σ) -∗ pointsto l α ==∗ own heapG_name (●V <[l:=(Next β)]>σ)
                                  ∗ pointsto l β.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]".
    { apply (gmap_view_update). }
    done.
  Qed.

  (** * The symbolic execution rules *)
  Lemma wp_read (l : loc) (α : IT) Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷▷ (pointsto l α -∗ WP@{rs} α {{ Φ }}) -∗
    WP@{rs} (READ l) {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    unfold READ. simpl.
    iApply wp_subreify'.
    iInv (nroot.@"storeE") as (σ) "[Hs Hh]" "Hcl".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hp"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [β' Hb'].
    iAssert (▷ (σ !! l ≡ Some (Next α)))%I as "#Hlookup".
    { iNext. iApply (istate_read with "Hh Hp"). }
    iAssert (▷ ▷ (β' ≡ α))%I as "#Hba".
    { iNext. rewrite Hx. rewrite option_equivI.
      rewrite Hb'. by iNext. }
    iClear "Hlookup".
    iModIntro. iExists σ,(Next β'),σ,β'.
    iFrame "Hs".
    repeat iSplit.
    - iAssert ((option_bind _ _ (λ x, Some (x, σ)) (σ !! l)) ≡
                 (option_bind _ _ (λ x, Some (x, σ)) (Some (Next β'))))%I as "H".
      + iApply (f_equivI with "[]").
        { intros k x1 y1 Hxy.
          apply option_mbind_ne; solve_proper. }
        iPureIntro. rewrite Hx Hb'//.
      + unfold mbind. iSimpl in "H". iRewrite "H". done.
    - iPureIntro. apply ofe_iso_21.
    - iNext. iNext. iIntros "Hs".
      iMod ("Hcl" with "[Hh Hs]") as "_".
      { iExists _. by iFrame. }
      iRewrite "Hba".
      by iApply ("Ha" with "Hp").
  Qed.
  Lemma wp_write (l : loc) (α β : IT) Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷▷ (pointsto l β -∗ Φ (NatV 0)) -∗
    WP@{rs} (WRITE l β) {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply wp_subreify'.
    iInv (nroot.@"storeE") as (σ) "[Hs Hh]" "Hcl".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hp"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [α' Ha'].
    iModIntro.
    iExists σ,(),(<[l:=Next β]>σ),(Nat 0).
    iFrame "Hs".
    iSimpl. repeat iSplit; [ done | done | ].
    iNext. iNext.
    iMod (istate_write _ _ β with "Hh Hp") as "[Hh Hp]".
    iIntros "Hs".
    iMod ("Hcl" with "[Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iApply wp_val. iModIntro.
    iApply ("Ha" with "Hp").
  Qed.
  Lemma wp_alloc (α : IT) (k : locO -n> IT) Φ `{!NonExpansive Φ} :
    heap_ctx -∗
    ▷▷ (∀ l, pointsto l α -∗ WP@{rs} k l {{ Φ }}) -∗
    WP@{rs} (ALLOC α k) {{ Φ }}.
  Proof.
    iIntros "Hh H".
    iApply wp_subreify'.
    iInv (nroot.@"storeE") as (σ) "[Hs Hh]" "Hcl".
    iModIntro.
    set (l:=Loc.fresh (dom σ)).
    iExists σ,l,_,(k l).
    iFrame "Hs".
    simpl. change (Loc.fresh (dom σ)) with l.
    iSplit; first done.
    iSplit.
    { rewrite ofe_iso_21. done. }
    iNext. iNext. iIntros "Hs".
    iMod (istate_alloc α l with "Hh") as "[Hh Hl]".
    { apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite -(Loc.add_0 l). apply Loc.fresh_fresh. lia. }
    iMod ("Hcl" with "[Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iApply ("H" with "Hl").
  Qed.

  (** * The logical relation *)
  Definition N := nroot.@"heh".
  Definition logrel_expr V (α : IT) : iProp :=
    (heap_ctx -∗ WP@{rs} α {{ V }})%I.

  Definition logrel_nat (βv : ITV) : iProp :=
    (∃ n, βv ≡ NatV n)%I.
  Definition logrel_arr V1 V2 (βv : ITV) : iProp :=
    (∃ f, IT_of_V βv ≡ Fun f ∧ □ ∀ αv, V1 αv -∗
       logrel_expr V2 (APP' (Fun f) (IT_of_V αv)))%I.
  Definition logrel_ref V (l : loc) : iProp :=
    (inv (N.@l) (∃ βv, pointsto l (IT_of_V βv) ∗ V βv))%I.

  Lemma logrel_alloc V V2 (αv :ITV) (k : locO -n> IT) `{!forall v, Persistent (V v)}
    `{NonExpansive V2} :
    V αv -∗
    (∀ l, logrel_ref V l -∗ logrel_expr V2 (k l)) -∗
    logrel_expr V2 (ALLOC (IT_of_V αv) k).
  Proof.
    iIntros "#HV H".
    iIntros "#Hh".
    iApply (wp_alloc with "Hh").
    iNext. iNext.
    iIntros (l) "Hl".
    iMod (inv_alloc (N.@l) _ (∃ βv, pointsto l (IT_of_V βv) ∗ V βv)%I with "[Hl]")
      as "#Hinv".
    { eauto with iFrame. }
    iSpecialize ("H" with "Hinv").
    by iApply "H".
  Qed.

  Lemma logrel_write V αv l `{!forall v, Persistent (V v)} :
    logrel_ref V l -∗
    V αv -∗
    logrel_expr logrel_nat (WRITE l (IT_of_V  αv)).
  Proof.
    iIntros "#Hl #Hav #Hctx".
    iApply wp_subreify'.
    iInv (nroot.@"storeE") as (σ) "[Hs Hh]" "Hcl1".
    iInv (N.@l) as "HH" "Hcl2".
    iDestruct "HH" as (βv) "[Hbv #HV]".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hbv"). }
    iModIntro.
    iExists σ, (),(<[l:=Next (IT_of_V αv)]>σ),(Nat 0).
    iFrame "Hs".
    iSimpl. repeat iSplit; [ done | done | ].
    iNext. iNext. iIntros "Hs".
    iMod (istate_write _ _ (IT_of_V αv) with "Hh Hbv") as "[Hh Hlav]".
    iMod ("Hcl2" with "[Hlav]") as "_".
    { iNext. iExists _; by iFrame. }
    iMod ("Hcl1" with "[Hh Hs]") as "_".
    { iNext. iExists _; by iFrame. }
    iModIntro.
    iApply wp_val. iModIntro.
    iExists 0. done.
  Qed.

  Lemma logrel_read V l `{!forall v, Persistent (V v)} :
    logrel_ref V l -∗
    logrel_expr V (READ l).
  Proof.
    iIntros "#Hr #Hctx".
    iApply wp_subreify'.
    iInv (nroot.@"storeE") as (σ) "[Hs Hh]" "Hcl1".
    iInv (N.@l) as "HH" "Hcl2".
    iDestruct "HH" as (βv) "[Hbv #HV]".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hbv"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [β' Hb'].
    iAssert (▷ (σ !! l ≡ Some (Next (IT_of_V βv))))%I as "#Hlookup".
    { iNext. iApply (istate_read with "Hh Hbv"). }
    iAssert (▷ ▷ (β' ≡ IT_of_V βv))%I as "#Hbv'".
    { iNext. rewrite Hx. rewrite option_equivI.
      rewrite Hb'. by iNext. }
    iClear "Hlookup".
    iModIntro. iSimpl.
    iExists σ,(Next β'),σ,β'. iFrame "Hs".
    repeat iSplit.
    { iPureIntro. rewrite Hx/= Hb'. done. }
    { rewrite ofe_iso_21//. }
    iNext. iNext. iIntros "Hs".
    iMod ("Hcl2" with "[Hbv]") as "_".
    { iNext. eauto with iFrame. }
    iMod ("Hcl1" with "[Hh Hs]") as "_".
    { iNext. eauto with iFrame. }
    iModIntro.
    iRewrite "Hbv'".
    iApply wp_val.
    iModIntro. done.
  Qed.

End wp.
