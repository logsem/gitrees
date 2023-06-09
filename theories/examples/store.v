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
Definition reify_store : reify_eff storeE stateF.
Proof.
  intros op X HX.
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
  Context {E : opsInterp}.
  Variable (rs : reifiers E).
  Notation IT := (IT E).
  Notation ITV := (ITV E).
  Notation stateO := (stateF ♯ IT).

  Context `{!subReifier reify_store rs rest}.
  Context `{!invGS_gen hlc Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).

  (* a separate ghost state for keeping track of locations *)
  Definition istate := gmap_viewUR loc (laterO IT).
  Context `{!inG Σ (istate)}.
  Variable γ : gname.

  Definition has_istate σ := own γ (●V σ).
  Definition pointsto (l : loc) (α : IT) : iProp :=
    own γ $ gmap_view_frag l (DfracOwn 1) (Next α).

  (* this is a bit useless as of now? *)
  Lemma wp_read (σ : stateO) σr (l : loc) (α : IT) Φ :
    σ !! l ≡ Some (Next α) →
    has_state (subState_conv_state σr σ) -∗
    has_istate σ -∗
    pointsto l α -∗
    (has_state (subState_conv_state σr σ) -∗
     has_istate σ -∗
     
                          ▷ WP@{rs} α {{ Φ }}) -∗
    WP@{rs} (READ l) {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold READ. simpl.
    iApply (wp_subreify with "Hs Ha").
    { simpl. trans (Some (Next α) ≫= (λ x : laterO IT, Some (x, σ))).
      - apply option_bind_proper; solve_proper.
      - simpl. reflexivity. }
    { apply ofe_iso_21. }
  Qed.
  Lemma wp_alloc (σ : stateO) σr (l : loc) (α : IT) Φ :
    σ !! l ≡ Some (Next α) →
    has_state (subState_conv_state σr σ) -∗
    (has_state (subState_conv_state σr σ) -∗ ▷ WP@{rs} α {{ Φ }}) -∗
    WP@{rs} (READ l) {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold READ. simpl.
    iApply (wp_subreify with "Hs Ha").
    { simpl. trans (Some (Next α) ≫= (λ x : laterO IT, Some (x, σ))).
      - apply option_bind_proper; solve_proper.
      - simpl. reflexivity. }
    { apply ofe_iso_21. }
  Qed.

End wp.

Section logrel.
  Context {E : opsInterp}.
  Variable (rs : reifiers E).
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Context `{!subReifier reify_store rs rest}.
  Context `{!invGS_gen hlc Σ, !stateG rs Σ}.
  Notation iProp := (iProp Σ).
  Notation restO := (rest ♯ IT).
  Notation stateO := (stateF ♯ IT).

  Implicit Type σ : stateO.
  Implicit Type α β : IT.
  Implicit Type l : loc.

  (* a separate ghost state for keeping track of locations *)
  Definition istate := gmap_viewUR loc (laterO IT).
  Context `{!inG Σ (istate)}.
  Variable γ : gname.

  Definition logrel_inv (σ : stateO) (r : restO) : iProp :=
    (has_state (subState_conv_state r σ) ∗ has_istate γ σ).

  #[local] Instance logrel_inv_ne : NonExpansive2 logrel_inv.
  Proof. unfold logrel_inv, has_state. solve_proper. Qed.

  #[local] Lemma istate_alloc α l σ :
    σ !! l = None →
    own γ (●V σ) ==∗ own γ (●V (<[l:=(Next α)]>σ))
                   ∗ pointsto l α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { apply (gmap_view_alloc _ l (DfracOwn 1) (Next α)); eauto.
      done. }
    done.
  Qed.

  #[local] Lemma istate_read l α σ :
    own γ (●V σ) -∗ pointsto l α -∗ σ !! l ≡ Some (Next α).
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[_ Hval]". done.
  Qed.

  #[local] Lemma istate_loc_dom l α σ :
    own γ (●V σ) -∗ pointsto l α -∗ ⌜is_Some (σ !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (istate_read with "Hinv Hloc") as "Hl".
    destruct (σ !! l) ; eauto.
    by rewrite option_equivI.
  Qed.

  #[local] Lemma istate_write l α β σ :
    own γ (●V σ) -∗ pointsto l α ==∗ own γ (●V <[l:=(Next β)]>σ)
                                  ∗ pointsto l β.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]".
    { apply (gmap_view_update). }
    done.
  Qed.

  Definition N := nroot.@"heh".
  Definition logrel_expr V (α : IT) : iProp :=
    (∀ (σ : stateO) (σr : restO),
        logrel_inv σ σr -∗ (* has_state (.. , sigma) * our_heap sigma *)
        WP@{rs} α {{ βv, ∃ σ', V βv ∗ logrel_inv σ' σr }})%I.

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
    iIntros (σ σr) "Hst".
    iDestruct "Hst" as "[H1 H2]".
    set (l:=Loc.fresh (dom σ)).
    iApply (wp_subreify with "H1").
    { simpl. change (Loc.fresh (dom σ)) with l.
      reflexivity. }
    { simpl. rewrite ofe_iso_21. reflexivity. }
    iIntros "Hs".
    iNext. iApply fupd_wp.
    { solve_proper. }
    iMod (istate_alloc (IT_of_V αv) l with "H2") as "[H3 Hr]".
    { apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite -(Loc.add_0 l). apply Loc.fresh_fresh. lia. }
    iMod (inv_alloc (N.@l) _ (∃ βv, pointsto l (IT_of_V βv) ∗ V βv)%I with "[Hr]")
      as "#Hinv".
    { eauto with iFrame. }
    iSpecialize ("H" with "Hinv").
    iModIntro. iApply "H".
    rewrite /logrel_inv. by iFrame.
  Qed.

  Lemma logrel_write V αv l `{!forall v, Persistent (V v)} :
    logrel_ref V l -∗
    V αv -∗
    logrel_expr logrel_nat (WRITE l (IT_of_V  αv)).
  Proof.
    iIntros "#Hl #Hav".
    iIntros (σ σr) "Hst".
    iDestruct "Hst" as "[H1 H2]".
    iApply (wp_reify_annoying with "H1").
    iInv (N.@l) as "HH" "Hcl".
    iDestruct "HH" as (βv) "[Hbv #HV]".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "H2 Hbv"). }
    iModIntro.
    iExists (Nat 0),(subState_conv_state σr (<[l:=Next (IT_of_V αv)]>σ)).
    iSplit.
    { rewrite reify_vis_eq; last first.
      - rewrite subR_reify. simpl. done.
      - iPureIntro. f_equiv; eauto. }
    iNext. iNext.
    iMod (istate_write _ _ (IT_of_V αv) with "H2 Hbv") as "[H2 Hlav]".
    iMod ("Hcl" with "[Hlav]") as "_".
    { iNext. iExists _; by iFrame. }
    iModIntro. iIntros "Hs".
    iApply wp_val. iModIntro.
    iExists _. iFrame "H2 Hs".
    iExists 0. done.
  Qed.

  Lemma logrel_read V l `{!forall v, Persistent (V v)} :
    logrel_ref V l -∗
    logrel_expr V (READ l).
  Proof.
    iIntros "#Hr".
    iIntros (σ σr) "[Hst Hgst]".
    unfold logrel_ref.

    iApply (wp_reify_annoying with "Hst").
    rewrite /logrel_ref.
    iInv (N.@l) as "HH" "Hcl".
    iDestruct "HH" as (βv) "[Hbv #HV]".
    iAssert (▷ ⌜is_Some (σ !! l)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hgst Hbv"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [β' Hb'].
    iAssert (▷ (σ !! l ≡ Some (Next (IT_of_V βv))))%I as "#Hlookup".
    { iNext. iApply (istate_read with "Hgst Hbv"). }
    iAssert (▷ ▷ (β' ≡ IT_of_V βv))%I as "#Hbv'".
    { iNext. rewrite Hx. rewrite option_equivI.
      rewrite Hb'. by iNext. }
    iClear "Hlookup".
    iModIntro.
    iExists β',(subState_conv_state σr σ).
    iSplit.
    { rewrite reify_vis_eq; last first.
      - rewrite subR_reify. simpl.
        rewrite Hx /=. done.
      - rewrite ofe_iso_21.
        rewrite Hb'. rewrite Tick_eq. done. }
    iNext. iNext.
    iMod ("Hcl" with "[Hbv]") as "_".
    { iNext. eauto with iFrame. }
    iModIntro.
    iIntros "Hst".
    iRewrite "Hbv'".
    iApply wp_val.
    iModIntro. iExists σ.
    by iFrame.
  Qed.

End logrel.
