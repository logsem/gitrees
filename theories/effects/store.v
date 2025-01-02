(** Higher-order store effect *)
From iris.algebra Require Import gmap excl auth gmap_view list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.
From gitrees Require Import prelude.
From gitrees Require Import gitree.
From gitrees.lib Require Import eq.

Opaque laterO_map.

(** State and operations *)
Canonical Structure locO := leibnizO loc.
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

Definition state_alloc X `{!Cofe X} : (laterO X) * (stateF ♯ X) → option (loc * (stateF ♯ X) * listO (laterO X))
  := λ '(n,s), let l := Loc.fresh (dom s) in
               let s' := <[l:=n]>s in
               Some (l, s', []).
#[export] Instance state_alloc_ne X `{!Cofe X} :
  NonExpansive (state_alloc X : prodO _ (stateF ♯ X) → optionO (locO * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [m1 s1] [m2 s2]. simpl.
  intros [Hm Hs]. simpl in *.
  set (l1 := Loc.fresh (dom s1)).
  set (l2 := Loc.fresh (dom s2)).
  assert (l1 = l2) as ->.
  { unfold l1,l2. f_equiv. eapply gmap_dom_ne, Hs. }
  solve_proper.
Qed.

Definition state_cas X `{!Cofe X} : (loc * (laterO X) * (laterO X) * (laterO (X -n> X -n> X -n> (X * X)%type))) * (stateF ♯ X)
                                    -> option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '((l, w1, w2, h), σ), v ← σ !! l;
                             let r := later_ap (later_ap (later_ap h v) w1) w2 in
                             Some (later_map fst r, <[l := later_map snd r]>σ, []).
#[export] Instance state_cas_ne X `{!Cofe X} :
  NonExpansive (state_cas X : prodO _ (stateF ♯ X) → optionO (laterO X * (stateF ♯ X) * listO (laterO X))%type).
(* Proof. *)
(*   intros n [[[[m1 k1] p1] n1] s1] [[[[m2 k2] p2] n2] s2]. simpl. *)
(*   intros [[[[Hm Hk] Hp] Hn] Hs]. simpl in *. *)
(*   f_equiv. *)
(*   - intros ?? Hxy; simpl. *)
(*     do 3 f_equiv; first solve_proper. *)
(*     rewrite Hs Hm. *)
(*     do 3 f_equiv; solve_proper. *)
(*   - by rewrite Hs Hm. *)
(* Qed. *)
Admitted.

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
Program Definition CasE : opInterp := {|
  Ins := (locO * (▶ ∙) * (▶ ∙) * ▶ (∙ -n> ∙ -n> ∙ -n> (∙ * ∙)))%OF;
  Outs := (▶ ∙);
|}.

Definition storeE : opsInterp := @[ReadE;WriteE;AllocE;DeallocE;CasE].
Canonical Structure reify_store : sReifier NotCtxDep.
Proof.
  simple refine {| sReifier_ops := storeE |}.
  intros X HX op.
  destruct op as [[]|[[]|[[]|[|[|[]]]]]]; simpl.
  - simple refine (OfeMor (state_read X)).
  - simple refine (OfeMor (state_write X)).
  - simple refine (OfeMor (state_alloc X)).
  - simple refine (OfeMor (state_dealloc X)).
  - simple refine (OfeMor (state_cas X)).
Defined.

Section simple_constructors.
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

End simple_constructors.

Section compound_constructors.
  Context {E : opsInterp}.
  Context `{!subEff storeE E}.
  Context {R} `{!Cofe R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe natO R}.
  Context `{!Ofe_decide_eq R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Local Program Definition simple_compare : IT -n> IT -n> IT -n> (IT * IT)%type :=
    λne v w1 w2, ((safe_compare (A := R) (E := E) w1 v)
                   , IF (safe_compare (A := R) (E := E) w1 v) w2 v).
  Solve All Obligations with solve_proper.

  Program Definition CAS : locO -n> IT -n> IT -n> IT :=
    λne l w1 w2, Vis (E := E) (subEff_opid $ inr $ inr $ inr $ inr $ inl ())
                   (subEff_ins (F := storeE) (op := (inr $ inr $ inr $ inr $ inl ()))
                      (l, Next w1, Next w2,
                        (Next (simple_compare))))
                   (ofe_iso_2 (subEff_outs (F := storeE) (op := (inr $ inr $ inr $ inr $ inl ())))).
  (* Next Obligation. *)
  (*   intros ????? n; simpl. *)
  (*   intros ?? H. *)
  (*   f_equiv. *)
  (*   solve_proper. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros ???? n; simpl. *)
  (*   intros ?? H ?; simpl. *)
  (*   solve_proper. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros ??? n; simpl. *)
  (*   intros ?? H; simpl. *)
  (*   intros ??; simpl. *)
  (*   solve_proper. *)
  (* Qed. *)
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

End compound_constructors.

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
  Context `{!invGS_gen HasLc Σ, !stateG rs R Σ}.
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
  Lemma istate_read l α σ :
    own heapG_name (●V (fmap (M := gmap locO) to_agree σ)) -∗ pointsto l α
    -∗ (σ !! l) ≡ Some (Next α).
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[%H [G Hval]]".
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
    apply gmap_view_replace.
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
      by iFrame.
    }
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

End wp.

Arguments heapG {_} {_} rs R {_} Σ.
Arguments heapPreG {_} {_} rs R {_} Σ.
Arguments heapΣ {_} {_} rs R {_}.
Arguments heap_ctx {_ _} rs {_ _ _ _ _ _ _}.
Arguments pointsto {_ _ _ _ _ _ _} _ _.
#[global]  Opaque ALLOC READ WRITE DEALLOC.

Section wp.
  Context {n : nat}.
  Context {a : is_ctx_dep}.
  Variable (rs : gReifiers a n).
  Context {R} {CR : Cofe R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe natO R}.
  Context `{!Ofe_decide_eq R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).
  Context `{!subReifier (sReifier_NotCtxDep_min reify_store a) rs}.
  Context `{!invGS_gen HasLc Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).
  Context `{!heapG rs R Σ}.

  Lemma wp_cas_fail_atomic_hom (l : loc) w1 `{!AsVal w1} w2 E1 E2 s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx rs -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ (safe_compare w1 α ≡ Ret 0) ∗
        ▷ ▷ (pointsto l α ={E2,E1}=∗ WP@{rs} (κ (Ret 0)) @ s {{ Φ }})) -∗
    WP@{rs} κ (CAS l w1 w2) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    unfold CAS; simpl.
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
    iExists σ,(Next (Ret 0)),σ,(κ (Ret 0)), [].
    iFrame "Hs".
    repeat iSplit.
    - rewrite /=.
      match goal with
      | |- context G [_ ≫= ?F] =>
          set (F' := F)
      end.
      iApply (internal_eq_rewrite _ _
                (λ x : option (later IT), (x ≫= F' ≡ Some (Next (Ret 0), σ, []))%I) with "[Hlookup]").
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
              -- f_equiv.
                 apply H; lia.
              -- f_equiv.
                 ++ f_equiv.
                    apply H; lia.
                 ++ apply H; lia.
          + do 2 f_equiv.
            apply Next_contractive.
            destruct m.
            * apply dist_later_0.
            * apply dist_later_S.
              f_equiv.
              -- f_equiv.
                 apply H; lia.
              -- f_equiv.
                 ++ f_equiv.
                    apply H; lia.
                 ++ apply H; lia.
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
        rewrite !later_map_Next /=.
        iApply option_equivI.
        iApply prod_equivI.
        iSplit; last done.
        iApply prod_equivI.
        iSplit.
        - iModIntro.
          iRewrite "Hcond".
          done.
        - rewrite /=.
          iRewrite "Hcond".
          iAssert (Next (IF (Ret 0) w2 α) ≡ Next α)%I as "HEQ"; last iRewrite "HEQ".
          { rewrite IF_False; [done | lia]. }
          iApply gmap_equivI.
          iIntros (i).
          destruct (decide (i = l)) as [Heq |].
          + rewrite Heq; clear Heq i.
            rewrite lookup_insert Hx'.
            iRewrite "Hlookup".
            done.
          + by rewrite lookup_insert_ne; last done.
      }
    - iPureIntro. by rewrite /= ofe_iso_21 laterO_map_Next.
    - iNext. iIntros "Hlc Hs".
      iMod ("Hback" with "Hp") as "Hback".
      iMod "Hwk" .
      iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
      { iExists _. by iFrame. }
      iModIntro.
      iSplit; last done.
      iApply "Hback".
  Qed.

  Lemma wp_cas_succ_atomic_hom (l : loc) w1 `{!AsVal w1} w2 E1 E2 s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx rs -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ (safe_compare w1 α ≡ Ret 1) ∗
        ▷ ▷ (pointsto l w2 ={E2,E1}=∗ WP@{rs} (κ (Ret 1)) @ s {{ Φ }})) -∗
    WP@{rs} κ (CAS l w1 w2) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H".
    unfold CAS; simpl.
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
    iExists σ,(Next (Ret 1)),(<[l := Next w2]>σ),(κ (Ret 1)), [].
    iFrame "Hs".
    repeat iSplit.
    - rewrite /=.
      match goal with
      | |- context G [_ ≫= ?F] =>
          set (F' := F)
      end.
      iApply (internal_eq_rewrite _ _
                (λ x : option (later IT), (x ≫= F' ≡ Some (Next (Ret 1), (<[l:=Next w2]>σ), []))%I) with "[Hlookup]").
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
              -- f_equiv.
                 apply H; lia.
              -- f_equiv.
                 ++ f_equiv.
                    apply H; lia.
                 ++ apply H; lia.
          + do 2 f_equiv.
            apply Next_contractive.
            destruct m.
            * apply dist_later_0.
            * apply dist_later_S.
              f_equiv.
              -- f_equiv.
                 apply H; lia.
              -- f_equiv.
                 ++ f_equiv.
                    apply H; lia.
                 ++ apply H; lia.
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
        rewrite !later_map_Next /=.
        iApply option_equivI.
        iApply prod_equivI.
        iSplit; last done.
        iApply prod_equivI.
        iSplit.
        - iModIntro.
          iRewrite "Hcond".
          done.
        - rewrite /=.
          iRewrite "Hcond".
          iAssert (Next (IF (Ret 1) w2 α) ≡ Next w2)%I as "HEQ"; last iRewrite "HEQ".
          { rewrite IF_True; [done | lia]. }
          done.
      }
    - iPureIntro. rewrite /= ofe_iso_21 laterO_map_Next //.
    - iNext. iIntros "Hlc Hs".
      iMod (istate_write _ _ α w2 with "Hh Hp") as "[Hh Hp]".
      iMod ("Hback" with "Hp") as "Hback".
      iMod "Hwk" .
      iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
      { iExists _. rewrite -(fmap_insert to_agree σ). by iFrame. }
      iModIntro. by iFrame.
  Qed.

End wp.

#[global] Opaque CAS.
