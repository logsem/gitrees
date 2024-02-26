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

Definition state_dealloc X `{!Cofe X} : loc * (stateF ♯ X) → option (unitO * (stateF ♯ X))
  := λ '(l,σ), Some ((), delete l σ).
#[export] Instance state_dealloc_ne X `{!Cofe X} :
  NonExpansive (state_dealloc X : prodO locO (stateF ♯ X) → optionO (prodO unitO (stateF ♯ X))).
Proof.
  intros n [l1 s1] [l2 s2]. simpl. intros [-> Hs].
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
Program Definition DeallocE : opInterp :=  {|
  Ins := locO;
  Outs := unitO;
|}.

Definition storeE : opsInterp := @[ReadE;WriteE;AllocE;DeallocE].
Canonical Structure reify_store : sReifier NotCtxDep.
Proof.
  simple refine {| sReifier_ops := storeE |}.
  intros X HX op.
  destruct op as [[]|[[]|[[]|[|[]]]]]; simpl.
  - simple refine (OfeMor (state_read X)).
  - simple refine (OfeMor (state_write X)).
  - simple refine (OfeMor (state_alloc X)).
  - simple refine (OfeMor (state_dealloc X)).
Defined.

Section constructors.
  Context {E : opsInterp}.
  Context `{!subEff storeE E}.
  Context {R} `{!Cofe R}.
  Context `{!SubOfe unitO R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Program Definition ALLOC : IT -n> (locO -n> IT) -n> IT :=
    (λne n k, Vis (E:=E) (subEff_opid $ inr (inr (inl ())))
      (subEff_ins (F:=storeE) (op:=inr (inr (inl ()))) (Next n))
      (NextO ◎ k ◎ (subEff_outs (F:=storeE) (op:=inr (inr (inl ()))))^-1)).
  Solve Obligations with solve_proper.

  Program Definition READ : locO -n> IT :=
    λne l, Vis (E:=E) (subEff_opid $ inl ())
                (subEff_ins (F:=storeE) (op:=(inl ())) l)
                ((subEff_outs (F:=storeE) (op:=(inl ())))^-1).


  Program Definition WRITE : locO -n> IT -n> IT :=
    λne l a, Vis (E:=E) (subEff_opid $ inr (inl ()))
                (subEff_ins (F:=storeE) (op:=(inr $ inl ())) (l,(Next a)))
                (λne _, Next (Ret ())).
  Solve Obligations with solve_proper.

  Program Definition DEALLOC : locO -n> IT :=
    λne l, Vis (E:=E) (subEff_opid $ inr $ inr $ inr $ inl ())
                (subEff_ins (F:=storeE) (op:=(inr $ inr $ inr $ inl ())) l)
                (λne _, Next (Ret ())).
End constructors.

Section wp.
  Context {n : nat}.
  Variable (rs : gReifiers NotCtxDep n).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe unitO R}.

  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).

  (* a separate ghost state for keeping track of locations *)
  Definition istate := gmap_viewUR loc (laterO IT).
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

  Context `{!subReifier reify_store rs}.
  Context `{!invGS_gen HasLc Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  (** * The ghost state theory for the heap *)

  Context `{!heapG Σ}.

  Definition heap_ctx := inv (nroot.@"storeE")
                        (∃ σ, £ 1 ∗ has_substate σ ∗ own heapG_name (●V σ))%I.
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
  Lemma istate_delete l α σ :
    own heapG_name (●V σ) -∗ pointsto l α ==∗ own heapG_name (●V delete l σ).
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "$".
    { apply (gmap_view_delete). }
    done.
  Qed.

  (** * The symbolic execution rules *)
  Lemma wp_read_atomic (l : loc)  E1 E2 s Φ :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (pointsto l α ={E2,E1}=∗ WP@{rs} α @ s {{ Φ }})) -∗
    WP@{rs} READ l @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    unfold READ. simpl.
    iApply wp_subreify_ctx_indep'. simpl.
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
    iExists σ,(Next β'),σ,β'.
    iFrame "Hs".
    repeat iSplit.
    - assert ((option_bind _ _ (λ x, Some (x, σ)) (σ !! l)) ≡
                (option_bind _ _ (λ x, Some (x, σ)) (Some (Next β')))) as <-.
      { rewrite Hx /= ; solve_proper. }
      simpl. iPureIntro. by f_equiv.
    - iPureIntro. apply ofe_iso_21.
    - iNext. iIntros "Hlc Hs".
      iMod ("Hback" with "Hp") as "Hback".
      iMod "Hwk" .
      iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
      { iExists _. by iFrame. }
      iRewrite "Hba". done.
  Qed.

  Lemma wp_read (l : loc) (α : IT) s Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ (pointsto l α -∗ WP@{rs} α @ s {{ Φ }}) -∗
    WP@{rs} READ l @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    iApply (wp_read_atomic _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext. iIntros "Hl".
    iModIntro. by iApply "Ha".
  Qed.

  Lemma wp_write_atomic (l : loc)  E1 E2 β s Φ :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (pointsto l β ={E2,E1}=∗ Φ (RetV ()))) -∗
    WP@{rs} WRITE l β @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    iApply wp_subreify_ctx_indep'. simpl.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken E1).
    { set_solver. }
    iIntros "Hwk".
    iMod "H" as (α) "[Hp Hback]".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hp"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [α' Ha'].
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iExists σ,(),(<[l:=Next β]>σ),(Ret ()).
    iFrame "Hs".
    iSimpl. repeat iSplit; [ done | done | ].
    iNext. iIntros "Hlc".
    iMod (istate_write _ _ β with "Hh Hp") as "[Hh Hp]".
    iIntros "Hs".
    iMod ("Hback" with "Hp") as "Hback".
    iMod "Hwk" .
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iApply wp_val. iModIntro. done.
  Qed.

  Lemma wp_write (l : loc) (α β : IT) s Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷▷ (pointsto l β -∗ Φ (RetV ())) -∗
    WP@{rs} WRITE l β @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply (wp_write_atomic _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext. iIntros "Hl".
    iModIntro. by iApply "Ha".
  Qed.

  Lemma wp_alloc (α : IT) (k : locO -n> IT) s Φ `{!NonExpansive Φ} :
    heap_ctx -∗
    ▷▷ (∀ l, pointsto l α -∗ WP@{rs} k l @ s {{ Φ }}) -∗
    WP@{rs} ALLOC α k @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    iApply wp_subreify_ctx_indep'. simpl.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    set (l:=Loc.fresh (dom σ)).
    iExists σ,l,_,(k l).
    iFrame "Hs".
    simpl. change (Loc.fresh (dom σ)) with l.
    iSplit; first done.
    iSplit.
    { simpl. rewrite ofe_iso_21. done. }
    iNext. iIntros "Hlc Hs".
    iMod (istate_alloc α l with "Hh") as "[Hh Hl]".
    { apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite -(Loc.add_0 l). apply Loc.fresh_fresh. lia. }
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iApply ("H" with "Hl").
  Qed.

  Lemma wp_dealloc_atomic (l : loc)  E1 E2 s Φ :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (|={E2,E1}=> Φ (RetV ()))) -∗
    WP@{rs} DEALLOC l @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    iApply wp_subreify_ctx_indep'. simpl.
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
    iExists σ,(),(delete l σ),(Ret ()).
    iFrame "Hs".
    repeat iSplit; simpl; eauto.
    iNext. iIntros "Hlc Hs".
    iMod (istate_delete with "Hh Hp") as "Hh".
    iMod ("Hback") as "Hback".
    iMod "Hwk" .
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. by iFrame. }
    iModIntro. by iApply wp_val.
  Qed.

  Lemma wp_dealloc (l : loc) α s Φ :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ Φ (RetV ()) -∗
    WP@{rs} DEALLOC l @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hl H".
    iApply (wp_dealloc_atomic _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext.
    iModIntro. done.
  Qed.

End wp.

Arguments heapG {_} rs R {_} Σ.
Arguments heapPreG {_} rs R {_} Σ.
Arguments heapΣ {_} rs R {_}.
Arguments heap_ctx {_ _ _ _ _ _ _ _ _}.
Arguments pointsto {_ _ _ _ _ _} _ _.
#[global]  Opaque ALLOC READ WRITE DEALLOC.
