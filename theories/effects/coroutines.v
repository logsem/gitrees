(** Coroutines effects *)
From iris.algebra Require Import gmap excl auth gmap_view list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.
From gitrees Require Import prelude gitree hom.

Opaque laterO_map.

Canonical Structure locO := leibnizO loc.

Definition stateF : oFunctor :=
  ((gmapOF locO (optionOF (▶ ∙ -n> ▶ ∙)))
   * listOF (locO * (▶ ∙ -n> ▶ ∙)))%OF.

#[local] Instance state_inhabited X `{!Cofe X} : Inhabited (stateF ♯ X).
Proof. apply _. Qed.
#[local] Instance state_cofe X `{!Cofe X} : Cofe (stateF ♯ X).
Proof. apply _. Qed.

Program Definition CreateE : opInterp :=
  {|
    Ins := ▶ (∙ -n> ∙);
    Outs := locO;
  |}.
Program Definition ResumeE : opInterp :=
  {|
    Ins := locO * (▶ ∙) * ▶ (locO -n> ∙ -n> ∙);
    Outs := ▶ ∙;
  |}.
Program Definition LabelE : opInterp :=
  {|
    Ins := locO * (▶ ∙);
    Outs := ▶ ∙;
  |}.
Program Definition YieldE : opInterp :=
  {|
    Ins := ▶ ∙;
    Outs := ▶ ∙;
  |}.

Definition coroutine_create X `{!Cofe X}
  : laterO (X -n> X) * (stateF ♯ X) * (locO -n> laterO X)
    → option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '(n, (s1, s2), k), let l := Loc.fresh (dom s1) in
                   let s' := <[l := Some (laterO_ap n)]>s1 in
                   Some (k l, (s', s2), []).
#[export] Instance coroutine_create_ne X `{!Cofe X} :
  NonExpansive (coroutine_create X
      : prodO (prodO (laterO (X -n> X)) (stateF ♯ X)) (locO -n> laterO X)
        → optionO (laterO X * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [[p1 [q1 m1]] s1] [[p2 [q2 m2]] s2]. simpl.
  intros [[Hp [Hq Hm]] Hs]. simpl in *.
  set (l1 := Loc.fresh (dom q1)).
  set (l2 := Loc.fresh (dom q2)).
  assert (l1 = l2) as ->.
  { unfold l1,l2. f_equiv. eapply gmap_dom_ne, Hq. }
  do 3 f_equiv; first done.
  f_equiv; last done.
  f_equiv; last done.
  by rewrite Hp.
Qed.

Program Definition coroutine_resume X `{!Cofe X}
  : (locO * laterO X * laterO (locO -n> X -n> X)) * (stateF ♯ X) * (laterO X -n> laterO X)
    → option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '((l, x, h), (σ1, σ2), k),
    flip (mbind (M := option))
      (lookup l σ1 : optionO (optionO (laterO X -n> laterO X))) $ λ f,
    flip (mbind (M := option))
      (f : (optionO (laterO X -n> laterO X))) $ λ f,
    let res : laterO X := f x in
    let res := laterO_ap (laterO_ap h (Next l)) res in
    let res := k res in
    let σ' := <[l := None]>σ1 in
    Some (res, (σ', σ2), []).
#[export] Instance coroutine_resume_ne X `{!Cofe X} :
  NonExpansive (coroutine_resume X
      : prodO (prodO (locO * laterO X * laterO (locO -n> X -n> X)) (stateF ♯ X)) _
        → optionO ((laterO X) * (stateF ♯ X) * listO (laterO X)))%type.
Proof.
  intros n [[[[l1 q1] p1] [t1 m1]] s1] [[[[l2 q2] p2] [t2 m2]] s2]. simpl.
  intros [[[[Hl%leibnizO_leibniz Hq] Hp] [Ht Hm]] Hs]; simpl in *.
  rewrite Hl.
  eapply option_mbind_ne; last done.
  intros ?? Hxy.
  eapply option_mbind_ne; last done.
  intros ?? Hxy'.
  rewrite Hm Ht.
  do 4 f_equiv; first done.
  apply Next_contractive.
  destruct n; first apply dist_later_0.
  apply dist_later_S.
  f_equiv; first (apply Hp; lia).
  apply (compose (proj2 (dist_later_S _ _ _)) (later_car_anti_contractive (S n) (_ q1) (_ q2))).
  by f_equiv.
Qed.

Definition coroutine_label X `{!Cofe X}
  : (loc * laterO X) * (stateF ♯ X) * (laterO X -n> laterO X)
    → option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '((l, e), (s1, s2), k), Some (k e, (s1, (l, k) :: s2), []).
#[export] Instance coroutine_label_ne X `{!Cofe X} :
  NonExpansive (coroutine_label X
      : prodO (prodO (prodO locO _) (stateF ♯ _)) _
        → optionO (laterO X * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [[[l1 p1] [t1 m1]] s1] [[[l2 p2] [t2 m2]] s2]. simpl.
  intros [[[Hl%leibnizO_leibniz Hp] [Ht Hm]] Hs]. simpl in *.
  do 3 f_equiv; first solve_proper.
  by rewrite Hl Ht Hm Hs.
Qed.

Definition coroutine_yield X `{!Cofe X}
  : laterO X * (stateF ♯ X) * (laterO X -n> laterO X)
    → option (laterO X * (stateF ♯ X) * listO (laterO X))
  := λ '(e, (σ, σ'), k),
    match σ' with
    | [] => None
    | (l, k') :: σ' =>
        let σ := <[l := Some k]>σ in
        Some (k' e, (σ, σ'), [])
    end.
#[export] Instance coroutine_yield_ne X `{!Cofe X} :
  NonExpansive (coroutine_yield X
      : prodO (prodO (laterO X) (stateF ♯ _)) _
        → optionO (laterO X * (stateF ♯ X) * listO (laterO X))%type).
Proof.
  intros n [[p1 [t1 [| [x1 y1] m1]]] s1] [[p2 [t2 [| [x2 y2] m2]]] s2]; simpl;
    intros [[Hp [Ht Hm]] Hs]; simpl in *; [done | | |].
  - inversion Hm.
  - inversion Hm.
  - apply cons_dist_inj in Hm.
    destruct Hm as [[Hx%leibnizO_leibniz Hy] Hm]; simpl in *.
    rewrite Hp Hx Hm Ht Hs.
    by do 4 f_equiv.
Qed.

Definition CoroutineE : opsInterp := @[CreateE; ResumeE; LabelE; YieldE].

Program Canonical Structure reify_coroutines : sReifier CtxDep :=
  Build_sReifier CtxDep CoroutineE _ _ _ _.
Next Obligation.
  intros X HX op.
  destruct op as [[]|[[]|[[]|[|[]]]]]; simpl.
  - simple refine (OfeMor (coroutine_create X)).
  - simple refine (OfeMor (coroutine_resume X)).
  - simple refine (OfeMor (coroutine_label X)).
  - simple refine (OfeMor (coroutine_yield X)).
Defined.

Local Notation op_create := (inl ()).
Local Notation op_resume := (inr (inl ())).
Local Notation op_label := (inr (inr (inl ()))).
Local Notation op_yield := (inr (inr (inr (inl ())))).

Section constructors.
  Context {E : opsInterp}.
  Context `{!subEff CoroutineE E}.
  Context {R} `{!Cofe R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Program Definition CREATE : IT -n> (locO -n> IT) -n> IT :=
    (λne p k, Vis (E := E) (subEff_opid $ op_create)
      (subEff_ins (F := CoroutineE) (op := op_create) (Next (APP'_ne p)))
      (NextO ◎ k ◎ (subEff_outs (F := CoroutineE) (op := op_create))^-1)).
  Next Obligation.
    intros ? n.
    intros x y Hxy.
    f_equiv.
    by rewrite Hxy.
  Qed.
  Next Obligation.
    intros n x y Hxy ?; simpl.
    do 2 f_equiv.
    apply Next_contractive.
    destruct n; first apply dist_later_0.
    apply dist_later_S.
    f_equiv. intros ?; simpl.
    f_equiv.
    by apply dist_S.
  Qed.

  Program Definition LABEL : locO -n> IT -n> IT
    := λne l x,
           Vis (E := E) (subEff_opid $ op_label)
             (subEff_ins (F := CoroutineE) (op := op_label) (l, Next x))
             ((subEff_outs (F := CoroutineE) (op := op_label))^-1).
  Solve All Obligations with solve_proper.

  Program Definition RESUME : locO -n> IT -n> IT :=
    (λne l e, Vis (E := E) (subEff_opid $ op_resume)
      (subEff_ins (F := CoroutineE) (op := op_resume) (l, Next e, Next LABEL))
      ((subEff_outs (F := CoroutineE) (op := op_resume))^-1)).
  Solve All Obligations with solve_proper.

  Program Definition YIELD : IT -n> IT :=
    λne e, Vis (E := E) (subEff_opid $ op_yield)
      (subEff_ins (F := CoroutineE) (op := op_yield) (Next e))
      ((subEff_outs (F := CoroutineE) (op := op_yield))^-1).
  Solve All Obligations with solve_proper.

End constructors.

Section program_logic.
  Context {n : nat}.
  Variable (rs : gReifiers CtxDep n).
  Context R {CR : Cofe R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).

  Definition suspended_closures :=
    gmap_viewR loc (agreeR (optionO (laterO IT -n> laterO IT))).

  Definition continuation_stack :=
    authR (optionUR (exclR (listO (locO * (laterO IT -n> laterO IT))%type))).

  Class coroutinesPreG Σ :=
    CoroutinesPreG
      {
        suspendedPreG_inG :: inG Σ suspended_closures;
        stackPreG_inG :: inG Σ continuation_stack;
      }.

  Class coroutinesG Σ :=
    CoroutinesG
      {
        suspendedG_inG :: inG Σ suspended_closures;
        stackG_inG :: inG Σ continuation_stack;
        suspendedG_name : gname;
        stackG_name : gname;
      }.

  Definition coroutinesΣ : gFunctors :=
    gFunctors.app (GFunctor suspended_closures) (GFunctor continuation_stack).

  #[export] Instance subG_suspended_closures {Σ}
    : subG coroutinesΣ Σ → inG Σ suspended_closures.
  Proof. solve_inG. Qed.
  #[export] Instance subG_stack {Σ}
    : subG coroutinesΣ Σ → inG Σ continuation_stack.
  Proof. solve_inG. Qed.

  Lemma new_coroutinesState σ1 σ2 `{!coroutinesPreG Σ} :
    (⊢ |==> ∃ `{!coroutinesG Σ},
           own (A := suspended_closures) suspendedG_name (●V σ1)
           ∗ own stackG_name (● Excl' σ2) : iProp Σ)%I.
  Proof.
    iMod (own_alloc (●V σ1)) as (γ) "H".
    { apply gmap_view_auth_valid. }
    iMod (own_alloc (● Excl' σ2)) as (γ') "H'".
    { by apply auth_auth_valid. }
    pose (sg := {|
                 suspendedG_inG := _;
                 stackG_inG := _;
                 suspendedG_name := γ;
                 stackG_name := γ'
               |}).
    iModIntro. iExists sg. by iFrame.
  Qed.

  Context `{!subReifier reify_coroutines rs}.
  Context `{!gitreeGS_gen rs R Σ, !coroutinesG Σ}.
  Notation iProp := (iProp Σ).

  Program Definition pointsto (l : loc) (α : optionO (laterO IT -n> laterO IT))
    : iProp :=
    own suspendedG_name $ gmap_view_frag l (DfracOwn 1) (to_agree α).
  Global Instance pointsto_proper l : Proper ((≡) ==> (≡)) (pointsto l).
  Proof. solve_proper. Qed.
  Global Instance pointsto_ne l : NonExpansive (pointsto l).
  Proof. solve_proper. Qed.
  Notation "l ↦ α" := (pointsto l (Some α)) (at level 20, format "l ↦ α")
      : bi_scope.
  Notation "l ↦ 'nil'" := (pointsto l None) (at level 20, format "l ↦ nil")
      : bi_scope.

  Program Definition stack (l : listO (locO * (laterO IT -n> laterO IT))%type)
    : iProp
    := own stackG_name $ ◯ Excl' l.
  Global Instance stack_proper : Proper ((≡) ==> (≡)) stack.
  Proof. solve_proper. Qed.
  Global Instance stack_ne : NonExpansive stack.
  Proof. solve_proper. Qed.

  Program Definition coroutines_ctx :=
    inv (nroot.@"coroutines")
      (∃ σ, £ 1
            ∗ has_substate σ
            ∗ own suspendedG_name (●V (fmap (M := gmap locO) to_agree (fst σ)))
            ∗ own stackG_name (● Excl' (snd σ)))%I.

  Lemma suspended_alloc α l σ :
    σ !! l = None →
    own suspendedG_name (●V σ) ==∗ own suspendedG_name (●V (<[l:=to_agree $ Some α]>σ))
                   ∗ l ↦ α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { by apply (gmap_view_alloc _ l (DfracOwn 1) (to_agree $ Some α)); eauto. }
    done.
  Qed.

  Lemma suspended_read l α σ :
    own suspendedG_name (●V (fmap (M := gmap locO) to_agree σ)) -∗ l ↦ α
    -∗ (σ !! l) ≡ Some (Some α).
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[%H [Hval HEQ]]".
    rewrite lookup_fmap.
    rewrite option_equivI.
    destruct (σ !! l) as [o |] eqn:Heq.
    - rewrite Heq /=.
      rewrite agree_equivI.
      by iRewrite "HEQ".
    - rewrite Heq /=.
      done.
  Qed.

  Lemma suspended_loc_dom l α σ :
    own suspendedG_name (●V (fmap (M := gmap locO) to_agree σ)) -∗ l ↦ α
    -∗ ⌜is_Some (σ !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (suspended_read with "Hinv Hloc") as "Hl".
    destruct (σ !! l) ; eauto.
    by rewrite option_equivI.
  Qed.

  Lemma suspended_write l α β σ :
    own suspendedG_name (●V σ)
    -∗ pointsto l α
    ==∗ own suspendedG_name (●V <[l:=(to_agree $ β)]>σ)
      ∗ pointsto l β.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]"; last done.
    by apply gmap_view_replace.
  Qed.

  Lemma suspended_delete l α σ :
    own suspendedG_name (●V σ) -∗ l ↦ α ==∗ own suspendedG_name (●V delete l σ).
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "$".
    { apply (gmap_view_delete). }
    done.
  Qed.

  Lemma suspended_flush l α σ :
    own suspendedG_name (●V σ) -∗ l ↦ α
    ==∗ own suspendedG_name (●V <[l := to_agree None ]>σ) ∗ l ↦ nil.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]"; last done.
    by apply gmap_view_replace.
  Qed.

  Lemma stack_update l l' l'' :
    own stackG_name (● Excl' l)
    -∗ stack l'
    ==∗ own stackG_name (● Excl' l'')
      ∗ stack l''.
  Proof.
    iIntros "H G".
    iMod (own_update_2 with "H G") as "[$ $]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  Lemma stack_agree xs ys :
    own stackG_name (● (Excl' xs)) -∗ stack ys -∗ xs ≡ ys.
  Proof.
    iIntros "Hγ● Hγ◯".
    iDestruct (own_valid_2 with "Hγ● Hγ◯") as "J".
    iDestruct (auth_both_validI with "J") as "((%c & #J1) & J2)".
    rewrite /op /cmra_op /= /excl_op_instance /= /ucmra_op /=.
    iRewrite "J1" in "J2".
    iDestruct (uPred.cmra_valid_elim with "J2") as "%J".
    destruct c as [[c|] |].
    - iExFalso.
      iPureIntro.
      apply J.
    - iExFalso.
      iPureIntro.
      apply J.
    - iDestruct (option_equivI with "J1") as "J".
      by iDestruct (excl_equivI with "J") as "J'".
  Qed.

  Lemma wp_create_hom s Φ (κ : locO -n> IT) α k `{!IT_hom k} :
    coroutines_ctx -∗
    ▷▷ (∀ l, l ↦ later_ap (Next $ APP'_ne α) -∗ WP@{rs} k (κ l) @ s {{ Φ }}) -∗
    WP@{rs} k (CREATE α κ) @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt H".
    unfold CREATE. simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_dep'.
    iInv (nroot.@"coroutines") as (σ) "[>Hlc [Hs [Hh Hh']]]" "Hcl".
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    set (l:=Loc.fresh (dom σ.1)).
    iExists σ, (Next (k (κ l))), (<[l := Some (later_ap (Next $ APP'_ne α))]>σ.1, σ.2),
      (k (κ l)), [].
    iFrame "Hs".
    destruct σ as [σ1 σ2]. simpl. change (Loc.fresh (dom σ1)) with l.
    iSplit.
    {
      iPureIntro.
      rewrite laterO_map_Next /=.
      do 3 f_equiv.
      by rewrite ofe_iso_21.
    }
    iSplit; first done.
    iNext. iIntros "Hlc Hs".
    iMod (suspended_alloc (later_ap (Next $ APP'_ne α)) l with "Hh") as "[Hh Hpt]".
    {
      apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite dom_fmap_L.
      rewrite -(Loc.add_0 l).
      apply Loc.fresh_fresh.
      lia.
    }
    iMod ("Hcl" with "[$Hlc Hs Hh Hh']") as "Hcl".
    {
      iNext. iExists (<[l := Some $ later_ap (Next $ APP'_ne α)]>σ1, σ2).
      rewrite fmap_insert.
      iFrame "Hs Hh Hh'".
    }
    iModIntro.
    iSplit; last done.
    iApply ("H" $! l with "Hpt").
  Qed.

  Lemma wp_resume_hom s Φ (l : loc) (e : IT) α k `{!IT_hom k} :
    coroutines_ctx
    -∗ l ↦ later_ap (Next $ α)
    -∗ ▷ (l ↦ nil -∗ WP@{rs} k (LABEL l (α e)) @ s {{ Φ }})
    -∗ WP@{rs} k (RESUME l e) @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt H G".
    unfold RESUME.
    iEval (rewrite hom_vis).
    iApply wp_subreify_ctx_dep'.
    iInv (nroot.@"coroutines") as (σ) "[>Hlc [Hs [Hh Hh']]]" "Hcl".
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    iAssert (⌜is_Some (σ.1 !! l)⌝)%I as "%Hdom".
    { iApply (suspended_loc_dom with "Hh H"). }
    destruct Hdom as [[x|] Hx];
      last (iExFalso;
            iDestruct (suspended_read with "Hh H") as "#J";
            rewrite Hx !option_equivI //=).
    destruct (Next_uninj (x (Next e))) as [β' Hb'].
    iDestruct (suspended_read with "Hh H") as "#J".
    iAssert (Next β' ≡ later_ap (Next $ α) (Next e))%I as "#Hba".
    {
      rewrite -Hb' Hx.
      do 2 rewrite option_equivI.
      by iRewrite "J".
    }
    iExists σ, (Next (k (LABEL l β'))), (<[l := None]> σ.1, σ.2),
      (k (LABEL l β')), [].
    iFrame "Hs".
    destruct σ as [σ1 σ2].
    iSplit.
    {
      iEval (rewrite /= Hx /= ofe_iso_21 laterO_map_Next /=).
      iPureIntro.
      do 3 f_equiv; last done.
      do 5 f_equiv.
      rewrite -Hb'.
      done.
    }
    iSplit; first done.
    iNext. iIntros "Hlc Hs".
    iMod (suspended_flush with "Hh H") as "[Hh Hl]".
    iMod ("Hcl" with "[$Hlc Hs Hh Hh']") as "Hcl".
    {
      iNext. iExists (<[l := None]> σ1, σ2).
      rewrite fmap_insert /=.
      iFrame "Hs Hh Hh'".
    }
    iModIntro.
    iSplit; last done.
    iRewrite "Hba".
    by iApply "G".
  Qed.

  Lemma wp_label_hom m l e s Φ (k : IT → IT) `{!IT_hom k}
    : coroutines_ctx
      -∗ stack m
      -∗ ▷ (stack ((l, later_ap (Next (λne x, k x))) :: m)
            -∗ WP@{rs} k e @ s {{ Φ }})
      -∗ WP@{rs} k (LABEL l e) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hstack H".
    unfold LABEL.
    iEval (rewrite hom_vis).
    iApply wp_subreify_ctx_dep'.
    iInv (nroot.@"coroutines") as (σ) "[>Hlc [Hs [Hh Hh']]]" "Hcl".
    destruct σ as [σ1 σ2].
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    iSimpl in "Hh Hh'".
    iDestruct (stack_agree with "Hh' Hstack") as "#HEQstack".
    iRewrite "HEQstack" in "Hh'".
    iExists (σ1, σ2), (Next (k e)),
      (σ1, (l, laterO_ap (Next (λne x, k x))) :: m), (k e), [].
    iFrame "Hs".
    iSplit.
    {
      iRewrite "HEQstack".
      iPureIntro.
      simpl. do 3 f_equiv.
      - rewrite ofe_iso_21.
        by rewrite laterO_map_Next /=.
      - do 3 f_equiv.
        intros ?; simpl.
        rewrite ofe_iso_21.
        done.
    }
    iSplit; first done.
    iNext.
    iIntros "Hlc Hs".
    rewrite /wptp /=.
    iMod (stack_update _ _ ((l, laterO_ap (Next (λne x, k x))) :: m)
           with "Hh' Hstack") as "[Hh' Hstack]".
    iMod ("Hcl" with "[$Hlc Hs Hh Hh']") as "Hcl".
    {
      iNext. iExists (σ1, (l, laterO_ap (Next (λne x, k x))) :: m).
      iFrame "Hs Hh Hh'".
    }
    iModIntro.
    iSplit; last done.
    by iApply "H".
  Qed.

  Lemma wp_yield_hom α a l ls e s Φ (k : IT → IT) `{!IT_hom k}
    : coroutines_ctx
      -∗ stack ((l, later_ap (Next a)) :: ls)
      -∗ pointsto l α
      -∗ ▷ (stack ls -∗ l ↦ laterO_ap (Next (λne x, k x)) -∗ WP@{rs} a e @ s {{ Φ }})
      -∗ WP@{rs} k (YIELD e) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hstack Hcont H".
    unfold YIELD.
    iEval (rewrite hom_vis).
    iApply wp_subreify_ctx_dep'.
    iInv (nroot.@"coroutines") as (σ) "[>Hlc [Hs [Hh Hh']]]" "Hcl".
    destruct σ as [σ1 σ2].
    iApply (lc_fupd_elim_later with "Hlc").
    iModIntro.
    iSimpl in "Hh Hh'".
    iDestruct (stack_agree with "Hh' Hstack") as "#HEQstack".
    iRewrite "HEQstack" in "Hh'".
    iExists (σ1, σ2), (Next (a e)),
      (<[l:=Some $ laterO_ap (Next (λne x, k x))]>σ1, ls), (a e), [].
    iFrame "Hs".
    iSplit.
    {
      iRewrite "HEQstack".
      iSimpl.
      iPureIntro.
      do 4 f_equiv.
      match goal with
      | |- context G [<[l := ?a]>_] =>
          set (t1 := a)
      end.
      symmetry.
      match goal with
      | |- context G [<[l := ?a]>_] =>
          set (t2 := a)
      end.
      apply (insert_proper l t2 t1); last done.
      subst t1 t2.
      f_equiv.
      intros ?. simpl.
      by rewrite ofe_iso_21.
    }
    iSplit; first done.
    iNext.
    iIntros "Hlc Hs".
    rewrite /wptp /=.
    iMod (stack_update _ _ ls
           with "Hh' Hstack") as "[Hh' Hstack]".
    iMod (suspended_write with "Hh Hcont") as "[Hh Hcont]".
    iMod ("Hcl" with "[$Hlc Hs Hh Hh']") as "Hcl".
    {
      iNext. iExists (<[l:=Some $ laterO_ap (Next (λne x, k x))]>σ1, ls).
      iSimpl.
      rewrite fmap_insert.
      iFrame "Hs Hh Hh'".
    }
    iModIntro.
    iSplit; last done.
    by iApply ("H" with "Hstack Hcont").
  Qed.

End program_logic.

Opaque CREATE RESUME YIELD LABEL.
Notation "l ↦ α" := (pointsto _ _ l (Some α)) (at level 20, format "l ↦ α") : bi_scope.
Notation "l ↦ 'nil'" := (pointsto _ _ l None) (at level 20, format "l ↦ nil") : bi_scope.

Section lib.
  Context {n : nat}.
  Variable (rs : gReifiers CtxDep n).
  Context {R} {CR : Cofe R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).
  Context `{!subReifier reify_coroutines rs}.

  Program Definition THUNK α : IT := λit _, α.
  Global Instance THUNK_ne : NonExpansive THUNK.
  Proof.
    intros p x y Hxy.
    rewrite /THUNK.
    do 2 f_equiv.
    by intros ?; simpl.
  Qed.

  Program Definition INVOKE (l : loc) := (λit x : IT, RESUME l x).
  Solve All Obligations with solve_proper.
  Global Instance INVOKE_ne : NonExpansive INVOKE.
  Proof. solve_proper. Qed.

  Program Definition WRAP (f : IT) : IT :=
    CREATE f (λne l, INVOKE l).
  Solve All Obligations with solve_proper_please.
  Global Instance WRAP_ne : NonExpansive WRAP.
  Proof.
    intros p x y Hxy. rewrite /WRAP.
    by do 2 f_equiv.
  Qed.

  Context `{!gitreeGS_gen rs R Σ, !coroutinesG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma let_into_hom (α : IT) f :
    LET α f = LETCTX f α.
  Proof. reflexivity. Qed.

  Lemma seq_into_hom (α β : IT) :
    SEQ α β = SEQCtx β α.
  Proof. reflexivity. Qed.

  Lemma app_into_hom (α β : IT) :
    APP' α β = AppLSCtx β α.
  Proof. reflexivity. Qed.

  Lemma ccompose_eta (f g : IT → IT) (α : IT) :
    f (g α) = (f ∘ g) α.
  Proof. reflexivity. Qed.

  Lemma wp_wrap_hom (k : IT → IT) `{!IT_hom k}
    ls (f : IT) s
    Φ :
    coroutines_ctx rs R
    -∗ stack rs R ls
    -∗ ▷ (∀ l,
            l↦later_ap (Next (APP'_ne f))
            -∗ stack rs R ls
            -∗ WP@{rs} k (INVOKE l) @ s {{ Φ }})
    -∗ WP@{rs} k (WRAP f) @ s {{ Φ }}.
  Proof.
    iIntros "#HCtx Hstack H".
    iEval (rewrite /WRAP).
    iApply wp_create_hom; first done.
    do 2 iNext. iIntros (l) "Hl". iSimpl.
    iApply ("H" $! l with "Hl Hstack").
  Qed.

  Lemma wp_invoke_app_hom (k : IT → IT) `{!IT_hom k}
    ls (f : IT -n> IT) s
    Φ l α `{!AsVal α} :
    coroutines_ctx rs R
    -∗ l↦later_ap (Next $ f)
    -∗ stack rs R ls
    -∗ ▷ (l↦nil
          -∗ stack rs R ((l, later_ap (Next (λne x : IT, k x))) :: ls)
          -∗ WP@{rs} k (f α) @ s {{ Φ }})
    -∗ WP@{rs} k (INVOKE l ⊙ α) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hl Hst H".
    iEval (rewrite /INVOKE APP'_Fun_l /= -Tick_eq hom_tick).
    iApply wp_tick. iNext. iIntros "Hlc".
    iApply (wp_resume_hom with "Hctx Hl").
    iNext. iIntros "Hl".
    unshelve iApply (wp_label_hom with "Hctx Hst"); first tc_solve.
    iNext. iIntros "Hst".
    iApply ("H" with "Hl Hst").
  Qed.

  Opaque laterO_map.
  Local Program Definition REC_pre (body : IT -n> IT -n> IT)
    : laterO IT -n> IT :=
    λne self, Fun $ laterO_map (λne f x, body f x) self.
  Solve All Obligations with solve_proper.
  Local Definition REC body : IT := mmuu (REC_pre body).
  Local Lemma REC_unfold (body : IT -n> IT -n> IT) :
    REC body ≡ Fun $ Next $ body (REC body).
  Proof.
    rewrite /REC {1}mmuu_unfold /REC_pre /= laterO_map_Next /=.
    do 2 f_equiv. intros ?; simpl.
    reflexivity.
  Qed.
  Local Lemma REC_Val (body : IT -n> IT -n> IT) α `{!AsVal α} :
    REC body ⊙ α ≡ Tick $ body (REC body) α.
  Proof.
    rewrite /REC {1}mmuu_unfold /REC_pre /= laterO_map_Next /=.
    rewrite APP'_Fun_l /= -Tick_eq //=.
  Qed.
  Local Program Definition RECV_pre (body : IT -n> IT -n> IT)
    : laterO ITV -n> ITV :=
    λne self, FunV $ laterO_map (λne f x, body f x) (later_map IT_of_V self).
  Solve All Obligations with solve_proper.
  Local Definition RECV body : ITV := mmuu (RECV_pre body).
  Local Lemma RECV_unfold (body : IT -n> IT -n> IT) :
    IT_of_V (RECV body) ≡ Fun $ Next $ body (IT_of_V (RECV body)).
  Proof.
    rewrite /RECV {1}mmuu_unfold /RECV_pre /= laterO_map_Next /=.
    do 2 f_equiv. intros ?; simpl.
    reflexivity.
  Qed.
  Local Instance REC_val body : IntoVal (REC body) (RECV body).
  Proof.
    rewrite /IntoVal.
    apply bi.siProp.internal_eq_soundness.
    iLöb as "IH".
    iEval (rewrite REC_unfold RECV_unfold).
    iApply f_equivI.
    iNext.
    iApply f_equivI.
    iApply "IH".
  Qed.
  Transparent laterO_map.

  Program Definition generator_body (seed : IT) (succ : IT -n> IT)
    : IT := REC (λne g x, SEQ (YIELD x) (g ⊙ (succ x))) ⊙ seed.
  Solve All Obligations with solve_proper.

  Lemma generator_body_unfold seed `{!AsVal seed} succ
    : generator_body seed succ
        ≡ Tick (SEQ (YIELD seed) (generator_body (succ seed) succ)).
  Proof. rewrite {1}/generator_body REC_Val //=. Qed.

  Definition generator (seed : IT) (succ : IT -n> IT) : IT
    := WRAP (THUNK (generator_body seed succ)).

  Lemma generator_unfold seed `{!AsVal seed} succ
    : generator seed succ
        ≡ WRAP (THUNK ((SEQ (Tick (YIELD seed)) (generator_body (succ seed) succ)))).
  Proof.
    rewrite {1}/generator.
    apply equiv_dist.
    intros p.
    do 2 f_equiv.
    rewrite seq_into_hom hom_tick {1} generator_body_unfold //=.
  Qed.

  Program Local Definition example `{!SubOfe unitO R}
    (seed : IT) (succ : IT -n> IT)
    : IT :=
    LET (generator seed succ)
      (λne x,
        SEQ (x ⊙ (Ret ()))
          (x ⊙ (Ret ()))).
  Solve All Obligations with solve_proper.

  Local Lemma wp_example `{!SubOfe unitO R}
    (seed : IT) `{!AsVal seed} (succ : IT -n> IT)
    `{∀ x, AsVal x → AsVal (succ x)} ls
    Φ `{!NonExpansive Φ}
    : from_option Φ True (IT_to_V (succ seed))
      -∗ coroutines_ctx rs R
      -∗ stack rs R ls
      -∗ WP@{rs} example seed succ {{ Φ }}.
  Proof.
    iIntros "G #Hcor Hst".
    iEval (rewrite /example let_into_hom).
    iApply (wp_wrap_hom with "Hcor Hst").
    iNext. iIntros (l) "Hl Hst".
    iEval (rewrite /LETCTX /= LET_Val /= seq_into_hom).

    iApply (wp_invoke_app_hom (SEQCtx (INVOKE l ⊙ (Ret ()))) with "Hcor Hl Hst").
    iNext. iIntros "Hl Hst".
    iEval (rewrite -seq_into_hom /THUNK get_val_ITV /= get_fun_fun /=
           -Tick_eq seq_into_hom hom_tick).
    iApply wp_tick. iNext. iIntros "_".
    iEval (rewrite generator_body_unfold seq_into_hom hom_tick).
    iApply wp_tick. iNext. iIntros "_".
    iEval (rewrite ccompose_eta).
    unshelve iApply (wp_yield_hom with "Hcor Hst Hl"); first tc_solve.
    iNext. iIntros "Hst Hl". iSimpl.
    iEval (rewrite /SEQCtx SEQ_Val).

    iApply (wp_invoke_app_hom idfun with "Hcor Hl Hst").
    iNext. iIntros "Hl Hst". iSimpl.
    iEval (rewrite /SEQCtx SEQ_Val seq_into_hom generator_body_unfold hom_tick).
    iApply wp_tick. iNext. iIntros "_".
    iEval (rewrite seq_into_hom ccompose_eta).
    unshelve iApply (wp_yield_hom with "Hcor Hst Hl"); first tc_solve.
    iNext. iIntros "Hst Hl". iSimpl.

    assert (AsVal (succ seed)) as [v HVal].
    { apply _. }
    unshelve iDestruct (internal_eq_rewrite' (IT_to_V (succ seed)) (Some v)
                          (λne x, from_option Φ True%I x) with "G") as "J".
    - solve_proper.
    - iIntros "_". by rewrite -HVal IT_to_of_V.
    - done.
    - iApply wp_val'.
      + rewrite -HVal IT_to_of_V //=.
      + iApply "J".
  Qed.

End lib.
