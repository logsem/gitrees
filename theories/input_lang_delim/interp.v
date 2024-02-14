(* From Equations Require Import Equations. *)
From gitrees Require Import gitree.
From gitrees.input_lang_delim Require Import lang.
Require Import gitrees.lang_generic_sem.
From iris.algebra Require Import gmap excl auth gmap_view.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.

Require Import Binding.Lib.
Require Import Binding.Set.


(** * State *)

Definition stateF : oFunctor := (gmapOF unitO (▶ ∙))%OF.

#[local] Instance state_inhabited : Inhabited (stateF ♯ unitO).
Proof. apply _. Qed.
#[local] Instance state_cofe X `{!Cofe X} : Cofe (stateF ♯ X).
Proof. apply _. Qed.



(** * Signatures *)

Program Definition readE : opInterp :=  {|
  Ins := unitO;
  Outs := (▶ ∙);
|}.

Program Definition writeE : opInterp :=  {|
  Ins := (▶ ∙);
  Outs := unitO;
|}.

Program Definition callccE : opInterp :=
  {|
    Ins := ((▶ ∙ -n> ▶ ∙) -n> ▶ ∙);
    Outs := (▶ ∙);
  |}.
Program Definition throwE : opInterp :=
  {|
    Ins := (▶ ∙ * (▶ ∙ -n> ▶ ∙));
    Outs := Empty_setO;
  |}.


Definition delimE := @[readE; writeE; callccE; throwE].


Notation op_read := (inl ()).
Notation op_write := (inr (inl ())).
Notation op_callcc := (inr (inr (inl ()))).
Notation op_throw := (inr (inr (inr (inl ())))).


Section reifiers.

  Context {X} `{!Cofe X}.
  Notation state := (stateF ♯ X).


  Definition reify_read : unit * state * (laterO X -n> laterO X) →
                          option (laterO X * state)
    := λ '(u,σ,κ), x ← σ !! u;
  Some (κ x, σ).
  #[export] Instance reify_read_ne :
    NonExpansive (reify_read : prodO (prodO unitO state)
                                 (laterO X -n> laterO X) →
                               optionO (prodO (laterO X) state)).
  Proof.
    intros n[[]][[]][[]]. simpl in *.
    apply option_mbind_ne; first solve_proper.
    by rewrite H0.
  Qed.

  Definition reify_write : (laterO X) * state * (unitO -n> laterO X) →
                           option (laterO X * state)
    := λ '(n,s,κ), let s' := <[():=n]>s
                   in Some (κ (), s').
  #[export] Instance reify_write_ne :
    NonExpansive (reify_write : prodO (prodO _ state)
                                  (unitO -n> laterO X) →
                                optionO (prodO (laterO X) state)).
  Proof.
    intros n [[]] [[]] [[]]; simpl in *. solve_proper.
  Qed.


  Definition reify_callcc : ((laterO X -n> laterO X) -n> laterO X) *
                              state * (laterO X -n> laterO X) →
                            option (laterO X * state) :=
    λ '(f, σ, k), Some ((k (f k): laterO X), σ : state).
  #[export] Instance reify_callcc_ne :
    NonExpansive (reify_callcc :
      prodO (prodO ((laterO X -n> laterO X) -n> laterO X) state)
        (laterO X -n> laterO X) →
      optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. repeat f_equiv; auto. Qed.


  Definition reify_throw :
    ((laterO X * (laterO X -n> laterO X)) * state * (Empty_setO -n> laterO X)) →
    option (laterO X * state) :=
    λ '((e, k'), σ, _),
      Some ((k' e : laterO X), σ : state).
  #[export] Instance reify_throw_ne :
    NonExpansive (reify_throw :
        prodO (prodO (prodO (laterO X) (laterO X -n> laterO X)) state)
          (Empty_setO -n> laterO X) →
        optionO (prodO (laterO X) (state))).
  Proof.
    intros ?[[[]]][[[]]]?. rewrite /reify_throw.
    repeat f_equiv; apply H.
  Qed.

End reifiers.

Canonical Structure reify_delim : sReifier.
Proof.
  simple refine {|
             sReifier_ops := delimE;
             sReifier_state := stateF
           |}.
  intros X HX op.
  destruct op as [ | [ | [ | [| []]]]]; simpl.
  - simple refine (OfeMor (reify_read)).
  - simple refine (OfeMor (reify_write)).
  - simple refine (OfeMor (reify_callcc)).
  - simple refine (OfeMor (reify_throw)).
Defined.



Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff delimE E}.
  Context {subOfe0 : SubOfe natO A}.
  Context {subOfe1 : SubOfe unitO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).


  Program Definition READ : IT :=
    Vis (E:=E) (subEff_opid $ op_read)
      (subEff_ins (F:=delimE) (op:=op_read) ())
      ((subEff_outs (F:=delimE) (op:=op_read))^-1).


  Program Definition WRITE :  IT -n> IT :=
    λne a, Vis (E:=E) (subEff_opid $ op_write)
                (subEff_ins (F:=delimE) (op:=op_write) (Next a))
                (λne _, Next (Ret ())).
  Solve Obligations with solve_proper.


  Program Definition CALLCC_ : ((laterO IT -n> laterO IT) -n> laterO IT) -n>
                                (laterO IT -n> laterO IT) -n>
                                IT :=
    λne f k, Vis (E:=E) (subEff_opid op_callcc)
             (subEff_ins (F:=delimE) (op:=op_callcc) f)
             (k ◎ (subEff_outs (F:=delimE) (op:=op_callcc))^-1).
  Solve All Obligations with solve_proper.

  Program Definition CALLCC : ((laterO IT -n> laterO IT) -n> laterO IT) -n> IT :=
    λne f, CALLCC_ f (idfun).
  Solve Obligations with solve_proper.

  Lemma hom_CALLCC_ k e f `{!IT_hom f} :
    f (CALLCC_ e k) ≡ CALLCC_ e (laterO_map (OfeMor f) ◎ k).
  Proof.
    unfold CALLCC_.
    rewrite hom_vis/=.
    f_equiv. by intro.
  Qed.

  Program Definition THROW : IT -n> (laterO IT -n> laterO IT) -n> IT :=
    λne e k, Vis (E:=E) (subEff_opid op_throw)
               (subEff_ins (F:=delimE) (op:=op_throw)
                  (NextO e, k))
               (λne x, Empty_setO_rec _ ((subEff_outs (F:=delimE) (op:=op_throw))^-1 x)).
  Next Obligation.
    solve_proper_prepare.
    destruct ((subEff_outs ^-1) x).
  Qed.
  Next Obligation.
    intros; intros ???; simpl.
    repeat f_equiv. assumption.
  Qed.
  Next Obligation.
    intros ?????; simpl.
    repeat f_equiv; assumption.
  Qed.


End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_delim rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation state := (stateF ♯ IT).


  (* a separate ghost state for keeping track of locations *)
  Definition istate := gmap_viewUR unit (laterO IT).
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

  Context `{!invGS_gen HasLc Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  (** * The ghost state theory for the heap *)

  Context `{!heapG Σ}.

  Definition heap_ctx := inv (nroot.@"storeE")
                        (∃ σ, £ 1 ∗ has_substate σ ∗ own heapG_name (●V σ))%I.

  Definition pointsto (u : unit) (α : IT) : iProp :=
    own heapG_name $ gmap_view_frag u (DfracOwn 1) (Next α).



  Lemma istate_alloc α u σ :
    σ !! u = None →
    own heapG_name (●V σ) ==∗ own heapG_name (●V (<[u:=(Next α)]>σ))
                   ∗ pointsto u α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { apply (gmap_view_alloc _ u (DfracOwn 1) (Next α)); eauto.
      done. }
    done.
  Qed.
  Lemma istate_read u α σ :
    own heapG_name (●V σ) -∗ pointsto u α -∗ σ !! u ≡ Some (Next α).
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[_ Hval]". done.
  Qed.
  Lemma istate_loc_dom u α σ :
    own heapG_name (●V σ) -∗ pointsto u α -∗ ⌜is_Some (σ !! u)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (istate_read with "Hinv Hloc") as "Hl".
    destruct (σ !! u) ; eauto.
    by rewrite option_equivI.
  Qed.
  Lemma istate_write u α β σ :
    own heapG_name (●V σ) -∗ pointsto u α ==∗ own heapG_name (●V <[u:=(Next β)]>σ)
                                  ∗ pointsto u β.
  Proof.
    iIntros "H Hu".
    iMod (own_update_2 with "H Hu") as "[$ $]".
    { apply (gmap_view_update). }
    done.
  Qed.
  Lemma istate_delete u α σ :
    own heapG_name (●V σ) -∗ pointsto u α ==∗ own heapG_name (●V delete u σ).
  Proof.
    iIntros "H Hu".
    iMod (own_update_2 with "H Hu") as "$".
    { apply (gmap_view_delete). }
    done.
  Qed.


  (** * The symbolic execution rules *)

  (** ** READ *)

  Lemma wp_read_atomic (l : unit)  E1 E2 s Φ
    (k : IT -n> IT) `{!IT_hom k} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto l α ∗
        ▷ ▷ (pointsto l α ={E2,E1}=∗ WP@{rs} k α @ s {{ Φ }})) -∗
    WP@{rs} k READ @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H". rewrite hom_vis. simpl.
    match goal with
    | |- context G [Vis ?a ?b ?c] => assert (c ≡ laterO_map k ◎ subEff_outs (op:=op_read) ^-1) as ->
    end; first solve_proper.
    iApply wp_subreify'.
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
    iExists σ,(Next $ k β'),σ,(k β').
    iFrame "Hs".
    repeat iSplit.
    - assert ((option_bind _ _ (λ x, Some (laterO_map k x, σ)) (σ !! l)) ≡
                 (option_bind _ _ (λ x, Some (x, σ)) (Some (Next $ k β')))) as H.
      { rewrite Hx. simpl. rewrite Hb'. by rewrite later_map_Next. }
      simpl in H.
      rewrite <-H.
      unfold mbind.
      simpl.
      iPureIntro.
      f_equiv; last done.
      intros ???.
      do 2 f_equiv. rewrite H0.
      by rewrite ofe_iso_21.
    - done.
    - iNext. iIntros "Hlc Hs".
      iMod ("Hback" with "Hp") as "Hback".
      iMod "Hwk" .
      iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
      { iExists _. by iFrame. }
      iRewrite "Hba". done.
  Qed.

  Lemma wp_read (l : unit) (α : IT) s Φ
    (k : IT -n> IT) `{!IT_hom k} :
    heap_ctx -∗
    ▷ pointsto l α -∗
    ▷ ▷ (pointsto l α -∗ WP@{rs} k α @ s {{ Φ }}) -∗
    WP@{rs} k READ @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    iApply (wp_read_atomic _ (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext. iIntros "Hl".
    iModIntro. by iApply "Ha".
  Qed.

  (** ** WRITE *)

  Lemma wp_write_atomic  E1 E2 β s Φ
    (k : IT -n> IT) `{!IT_hom k} :
    nclose (nroot.@"storeE") ## E1 →
    heap_ctx -∗
    (|={E1,E2}=> ∃ α, ▷ pointsto () α ∗
        ▷ ▷ (pointsto () β ={E2,E1}=∗ WP@{rs} k (Ret ()) @ s {{ Φ }})) -∗
    WP@{rs} k (WRITE β) @ s {{ Φ }}.
  Proof.
    iIntros (Hee) "#Hcxt H". rewrite hom_vis. simpl.
    iApply wp_subreify'.
    iInv (nroot.@"storeE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iApply (fupd_mask_weaken E1).
    { set_solver. }
    iIntros "Hwk".
    iMod "H" as (α) "[Hp Hback]".
    iAssert (▷ ⌜is_Some (σ !! tt)⌝)%I as "#Hdom".
    { iNext. iApply (istate_loc_dom with "Hh Hp"). }
    iDestruct "Hdom" as ">%Hdom".
    destruct Hdom as [x Hx].
    destruct (Next_uninj x) as [α' Ha'].
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iExists σ, (Next $ k (Ret ())), (<[():=Next β]>σ), (k $ Ret ()).
    iFrame "Hs".
    iSimpl. repeat iSplit; [ by rewrite later_map_Next | done | ].
    iNext. iIntros "Hlc".
    iMod (istate_write _ _ β with "Hh Hp") as "[Hh Hp]".
    iIntros "Hs".
    iMod ("Hback" with "Hp") as "Hback".
    iMod "Hwk" .
    iMod ("Hcl" with "[Hlc Hh Hs]") as "_".
    { iExists _. iFrame. }
    done.
  Qed.

  Lemma wp_write (α β : IT) s Φ (k : IT -n> IT) `{!IT_hom k} :
    heap_ctx -∗
    ▷ pointsto () α -∗
    ▷▷ (pointsto () β -∗ WP@{rs} k (Ret ()) @ s {{ Φ }}) -∗
    WP@{rs} k $ WRITE β @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply (wp_write_atomic (⊤∖ nclose (nroot.@"storeE")) with "[$]").
    { set_solver. }
    iModIntro. iExists _; iFrame.
    iNext. iNext. iIntros "Hl".
    iModIntro. by iApply "Ha".
  Qed.


  (** ** THROW *)

  Lemma wp_throw' (σ : state) (f : laterO IT -n> laterO IT) (x : IT)
    (κ : IT -n> IT) `{!IT_hom κ} Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} later_car $ f (Next x) @ s {{ Φ }}) -∗
    WP@{rs} κ (THROW x f) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha". rewrite /THROW. simpl.
    rewrite hom_vis.
    destruct (Next_uninj (f (Next x))) as [α Hα].
    iApply (wp_subreify with "Hs"); simpl.
    + reflexivity.
    + apply Hα.
    + by assert (α ≡ later_car (f (Next x))) as -> by done.
  Qed.

  Lemma wp_throw (σ : state) (f : laterO IT -n> laterO IT) (x : IT) Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} later_car $ f $ Next x @ s {{ Φ }}) -∗
    WP@{rs} (THROW x f) @ s {{ Φ }}.
  Proof.
    iApply (wp_throw' _ _ _ idfun).
  Qed.

  (** ** CALL/CC *)

  Lemma wp_callcc (σ : state) (f : (laterO IT -n> laterO IT) -n> laterO IT)
    (k : IT -n> IT) {Hk : IT_hom k} Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k (later_car (f (laterO_map k))) @ s {{ Φ }}) -∗
    WP@{rs} (k (CALLCC f)) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold CALLCC. simpl.
    rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ ((later_map k ((f (laterO_map k))))) with "Hs").
    {
      simpl.
      repeat f_equiv.
      - rewrite ofe_iso_21.
        f_equiv. intro x. simpl.
        by rewrite ofe_iso_21.
      - reflexivity.
    }
    { by rewrite later_map_Next. }
    iModIntro.
    iApply "Ha".
  Qed.

End weakestpre.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_delim rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation state := (stateF ♯ IT).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Global Instance denot_cont_ne (κ : IT -n> IT) :
    NonExpansive (λ x : IT, Tau (laterO_map κ (Next x))).
  Proof.
    solve_proper.
  Qed.

  (** * Interpreting individual operators *)

  (** ** RESET *)
  Program Definition interp_reset (e : IT) : IT :=
    CALLCC (λne (k : laterO IT -n> laterO IT),
              Next $
              LET READ (λne m, SEQ
                                 (WRITE (λit r, SEQ (WRITE m) (THROW r k)))
                                 (APP' READ e))).
  Solve Obligations with solve_proper.
  Next Obligation.
    intros e k n ???. repeat f_equiv. intro. simpl. solve_proper.
  Qed.
  Next Obligation.
    intros e n ???. repeat f_equiv. by do 2 (intro; simpl; repeat f_equiv).
  Qed.

  #[export] Instance interp_reset_ne :
    NonExpansive (interp_reset).
  Proof.
    intros n ???. rewrite /interp_reset. simpl. repeat f_equiv.
    by do 2 (intro; simpl; repeat f_equiv).
  Qed.

  (** ** SHIFT *)
  Program Definition interp_shift {S}
    (e : @interp_scope F R _ (inc S) -n> IT) : interp_scope S -n> IT :=
    λne env, CALLCC (λne (k : laterO IT -n> laterO IT),
                       Next (APP'
                               READ
                               (e (@extend_scope F R _ _ env
                                     (λit x, interp_reset (THROW x k)))))).
  Next Obligation.
    intros S e env k n ???. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros S e env n ???. repeat f_equiv. intro. simpl. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros S e n ???. f_equiv. intro; simpl; repeat f_equiv.
    intros [|a]; simpl; last solve_proper.
    repeat f_equiv.
  Qed.


  (** ** NATOP *)
  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_natop.


  (** ** REC *)
  Opaque laterO_map.
  Program Definition interp_rec_pre {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT)
    : laterO (@interp_scope F R _ S -n> IT) -n> @interp_scope F R _ S -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : @interp_scope F R  _ S -n> IT) (a : IT),
                      body (@extend_scope F R _ _ (@extend_scope F R _ _ env (self env)) a)) self.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    do 3 f_equiv; intros ??; simpl; f_equiv;
    intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    by do 2 f_equiv.
  Qed.

  Program Definition interp_rec {S : Set}
    (body : @interp_scope F R _ (inc (inc S)) -n> IT) :
    @interp_scope F R _ S -n> IT :=
    mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set}
    (body : @interp_scope F R _ (inc (inc S)) -n> IT) env : IT -n> IT :=
    λne a, body (@extend_scope F R _ _
                   (@extend_scope F R _ _ env (interp_rec body env))
                   a).
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv. intros [| [| y']]; simpl; solve_proper.
  Qed.

  Lemma interp_rec_unfold {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT) env :
    interp_rec body env ≡ Fun $ Next $ ir_unf body env.
  Proof.
    trans (interp_rec_pre body (Next (interp_rec body)) env).
    { f_equiv. rewrite /interp_rec. apply mmuu_unfold. }
    simpl. rewrite laterO_map_Next. repeat f_equiv.
    simpl. unfold ir_unf. intro. simpl. reflexivity.
  Qed.


  (** ** APP *)
  Program Definition interp_app {A} (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, APP' (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_app_ne A : NonExpansive2 (@interp_app A).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_app.

  (** ** IF *)
  Program Definition interp_if {A} (t0 t1 t2 : A -n> IT) : A -n> IT :=
    λne env, IF (t0 env) (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  (** ** NAT *)
  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Ret n.

  (** ** CONT *)
  Program Definition interp_cont_val {S} (K : S -n> (IT -n> IT)) : S -n> IT :=
    λne env, (λit x, Tau (laterO_map (K env) (Next x))).
  Solve All Obligations with solve_proper_please.

  (* Program Definition interp_cont {S} (e : @interp_scope F R _ (inc S) -n> IT) : *)
  (*   interp_scope S -n> IT := *)
  (*   λne env, (Fun (Next (λne x, Tick $ e (@extend_scope F R _ _ env x)))). *)
  (* Next Obligation. *)
  (*   solve_proper_prepare. repeat f_equiv. *)
  (*   intros [|a]; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   solve_proper_prepare. *)
  (*   repeat f_equiv. *)
  (*   intro. simpl. repeat f_equiv. *)
  (*   intros [|z]; eauto. *)
  (* Qed. *)

  #[local] Instance interp_reset_full_ne {S} (f : @interp_scope F R _ S -n> IT):
    NonExpansive (λ env, interp_reset (f env)).
  Proof. solve_proper. Qed.

  Program Definition interp_ifk {A} (e1 e2 : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> (IT -n> IT) :=
  λne env b, (K env) $ interp_if (λne env, b) e1 e2 env.
  Solve All Obligations with solve_proper.

  Program Definition interp_apprk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app q (λne env, t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_applk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app (λne env, t) q env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoprk {A} (op : nat_op) (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_natop op q (λne env, t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoplk {A} (op : nat_op) (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_natop op (λne env, t) q env.
  Solve All Obligations with solve_proper.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | LitV n => interp_nat n
    | RecV e => interp_rec (interp_expr e)
    | ContV K => interp_cont_val (interp_cont K)
    end
  with
  interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | Val v => interp_val v
    | Var x => interp_var x
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
    | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
    | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
    | Shift e => interp_shift (interp_expr e)
    | Reset e => λne env, (OfeMor interp_reset) (interp_expr e env)
    end
  with
  interp_cont {S} (K : cont S) : interp_scope S -n> (IT -n> IT) :=
    match K with
    | END => λne env x, x
    | IfK e1 e2 K => interp_ifk (interp_expr e1) (interp_expr e2) (interp_cont K)
    | AppLK v K => interp_applk (interp_val v) (interp_cont K)
    | AppRK e K => interp_apprk (interp_expr e) (interp_cont K)
    | NatOpLK op v K => interp_natoplk op (interp_val v) (interp_cont K)
    | NatOpRK op e K => interp_natoprk op (interp_expr e) (interp_cont K)
    end.

  (* Definition interp_ectx_el {S} (C : ectx_el S) : *)
  (*   (interp_scope S -n> IT) -n> (interp_scope S) -n> IT := *)
  (*   match C with *)
  (*   | AppRK e1 => interp_apprk (interp_expr e1) *)
  (*   | AppLK e2 => interp_applk (interp_expr e2) *)
  (*   | NatOpRK op e1 => interp_natoprk op (interp_expr e1) *)
  (*   | NatOpLK op e2 => interp_natoplk op (interp_expr e2) *)
  (*   | IfK e1 e2 => interp_ifk (interp_expr e1) (interp_expr e2) *)
  (*   | ResetK => interp_resetk *)
  (*   end. *)


  (* Fixpoint interp_ectx' {S} (K : ectx S) : *)
  (*   interp_scope S -> IT -> IT := *)
  (*   match K with *)
  (*   | [] => λ env, idfun *)
  (*   | C :: K => λ (env : interp_scope S), λ (t : IT), *)
  (*                 (interp_ectx' K env) (interp_ectx_el C (λne env, t) env) *)
  (*   end. *)
  (* #[export] Instance interp_ectx_1_ne {S} (K : ectx S) (env : interp_scope S) : *)
  (*   NonExpansive (interp_ectx' K env : IT → IT). *)
  (* Proof. induction K; solve_proper_please. Qed. *)

  (* Definition interp_ectx'' {S} (K : ectx S) (env : interp_scope S) : IT -n> IT := *)
  (*   OfeMor (interp_ectx' K env). *)

  (* Lemma interp_ectx''_cons {S} (env : interp_scope S) *)
  (*   (K : ectx S) (C : ectx_el S) (x : IT) (n : nat) : *)
  (*   interp_ectx'' (C :: K) env x ≡{n}≡ interp_ectx'' K env (interp_ectx_el C (λne _, x) env). *)
  (* Proof. done. Qed. *)

  (* #[export] Instance interp_ectx_2_ne {S} (K : ectx S) : *)
  (*   NonExpansive (interp_ectx'' K : interp_scope S → (IT -n> IT)). *)
  (* Proof. *)
  (*   induction K; intros ????; try by intro. *)
  (*   intro. *)
  (*   rewrite !interp_ectx''_cons. *)
  (*   f_equiv. *)
  (*   - by apply IHK. *)
  (*   - by f_equiv. *)
  (* Qed. *)

  (* Definition interp_ectx {S} (K : ectx S) : interp_scope S -n> (IT -n> IT) := *)
  (*   OfeMor (interp_ectx'' K). *)

  (* Eval cbv[test_ectx interp_ectx interp_ectx' interp_ectx_el *)
  (*            interp_apprk interp_outputk interp_output interp_app] in (interp_ectx test_ectx). *)
  (* Definition interp_ectx {S} (K : ectx S) : interp_scope S -n> IT -n> IT := *)
  (*   λne env e, *)
  (*     (fold_left (λ k c, λne (e : interp_scope S -n> IT), *)
  (*                   (interp_ectx_el c env) (λne env, k e)) K (λne t : , t)) e. *)

  (* Open Scope syn_scope. *)

  (* Example callcc_ex : expr ∅ := *)
  (*   NatOp + (# 1) (Callcc (NatOp + (# 1) (Throw (# 2) ($ 0)))). *)
  (* Eval cbn in callcc_ex. *)
  (* Eval cbn in interp_expr callcc_ex *)
  (*               (λne (x : leibnizO ∅), match x with end). *)

  Global Instance interp_val_asval {S} {D : interp_scope S} (v : val S)
    : AsVal (interp_val v D).
  Proof.
    destruct v; simpl.
    - apply _.
    - rewrite interp_rec_unfold. apply _.
    - apply _.
  Qed.

  Global Instance ArrEquiv {A B : Set} : Equiv (A [→] B) :=
    fun f g => ∀ x, f x = g x.

  Global Instance ArrDist {A B : Set} `{Dist B} : Dist (A [→] B) :=
    fun n => fun f g => ∀ x, f x ≡{n}≡ g x.

  Global Instance ren_scope_proper {S S'} :
    Proper ((≡) ==> (≡) ==> (≡)) (@ren_scope F _ CR S S').
  Proof.
    intros D D' HE s1 s2 Hs.
    intros x; simpl.
    f_equiv.
    - apply Hs.
    - apply HE.
 Qed.

  Lemma interp_expr_ren {S S'} env
    (δ : S [→] S') (e : expr S) :
    interp_expr (fmap δ e) env ≡ interp_expr e (ren_scope δ env)
  with interp_val_ren {S S'} env
         (δ : S [→] S') (e : val S) :
    interp_val (fmap δ e) env ≡ interp_val e (ren_scope δ env)
  with interp_cont_ren {S S'} env
         (δ : S [→] S') (K : cont S) :
    interp_cont (fmap δ K) env ≡ interp_cont K (ren_scope δ env).
  Proof.
    - destruct e; simpl; try by repeat f_equiv.
      + repeat f_equiv. intro; simpl; repeat f_equiv.
        rewrite interp_expr_ren. f_equiv.
        intros [|a]; simpl; last done.
        by repeat f_equiv.
      + unfold interp_reset. repeat f_equiv.
        by repeat (intro; simpl; repeat f_equiv).
    - destruct e; simpl.
      + reflexivity.
      + clear -interp_expr_ren.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 1 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_ren.
        iApply f_equivI.
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done; last done.
        by iRewrite - "IH".
      + repeat f_equiv.
        intro. simpl. repeat f_equiv.
        apply interp_cont_ren.
    - destruct K; simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_ren || apply interp_val_ren || apply interp_cont_ren).
  Qed.


  (* Lemma interp_ectx_ren {S S'} env (δ : S [→] S') (K : ectx S) : *)
  (*   interp_ectx (fmap δ K) env ≡ interp_ectx K (ren_scope δ env). *)
  (* Proof. *)
  (*   induction K; intros ?; simpl; eauto. *)
  (*   destruct a; simpl; try (etrans; first by apply IHK); repeat f_equiv; *)
  (*      try solve [by apply interp_expr_ren | by apply interp_val_ren]. *)
  (* Qed. *)


  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : cont S):
    interp_expr (fill K e) env ≡ (interp_cont K) env ((interp_expr e) env).
  Proof. elim : K e env; eauto. Qed.

  Program Definition sub_scope {S S'} (δ : S [⇒] S') (env : interp_scope S')
    : interp_scope S := λne x, interp_expr (δ x) env.

  Global Instance SubEquiv {A B : Set} : Equiv (A [⇒] B) := fun f g => ∀ x, f x = g x.

  Global Instance sub_scope_proper {S S'} :
    Proper ((≡) ==> (≡) ==> (≡)) (@sub_scope S S').
  Proof.
    intros D D' HE s1 s2 Hs.
    intros x; simpl.
    f_equiv.
    - f_equiv.
      apply HE.
    - apply Hs.
 Qed.

  Lemma interp_expr_subst {S S'} (env : interp_scope S')
    (δ : S [⇒] S') e :
    interp_expr (bind δ e) env ≡ interp_expr e (sub_scope δ env)
  with interp_val_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') e :
    interp_val (bind δ e) env ≡ interp_val e (sub_scope δ env)
  with interp_cont_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') K :
    interp_cont (bind δ K) env ≡ interp_cont K (sub_scope δ env).
  Proof.
    - destruct e; simpl; try by repeat f_equiv.
      + repeat f_equiv. repeat (intro; simpl; repeat f_equiv).
        rewrite interp_expr_subst. f_equiv.
        intros [|a]; simpl; repeat f_equiv. rewrite interp_expr_ren.
        f_equiv. intro. done.
      + unfold interp_reset; repeat f_equiv. by repeat (intro; simpl; repeat f_equiv).
    - destruct e; simpl.
      + reflexivity.
      + clear -interp_expr_subst.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 1 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_subst.
        iApply f_equivI.
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done.
        * by iRewrite - "IH".
        * do 2 rewrite interp_expr_ren.
          iApply f_equivI.
          iApply internal_eq_pointwise.
          iIntros (z).
          done.
      + repeat f_equiv. intro. simpl. repeat f_equiv.
        by rewrite interp_cont_subst.
    - destruct K; simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_subst || apply interp_val_subst || apply interp_cont_subst).
  Qed.



  (** ** Interpretation is a homomorphism (for some constructors) *)

  #[global] Instance interp_cont_hom_emp {S} env :
    IT_hom (interp_cont (END : cont S) env).
  Proof.
    simple refine (IT_HOM _ _ _ _ _); intros; auto.
    simpl. f_equiv. intro. simpl.
    by rewrite laterO_map_id.
  Qed.


  #[global] Instance interp_cont_hom_if {S}
    (K : cont S) (e1 e2 : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (IfK e1 e2 K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite -hom_tick -IF_Tick.
    - trans (Vis op i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (IF t (interp_expr e1 env) (interp_expr e2 env)))
          y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      by rewrite -hom_vis.
    - trans (interp_cont K env (Err e)); first (f_equiv; apply IF_Err).
      apply hom_err.
  Qed.


  #[global] Instance interp_cont_hom_appr {S} (K : cont S)
    (e : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppRK e K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[global] Instance interp_cont_hom_appl {S} (K : cont S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppLK v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv. apply APP'_Tick_l. apply interp_val_asval.
    - trans (Vis op i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (t ⊙ (interp_val v env)))
          y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      by rewrite -hom_vis.
    - trans (interp_cont K env (Err e));
        first (f_equiv; apply APP'_Err_l; apply interp_val_asval).
      apply hom_err.
  Qed.

  #[global] Instance interp_cont_hom_natopr {S} (K : cont S)
    (e : expr S) op env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpRK op e K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[global] Instance interp_cont_hom_natopl {S} (K : cont S)
    (v : val S) op (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpLK op v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv. by rewrite -NATOP_ITV_Tick_l.
    - trans (Vis op0 i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (NATOP (do_natop op) t (interp_val v env))) y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      rewrite NATOP_ITV_Vis_l hom_vis. f_equiv. intro. simpl.
      by rewrite -laterO_map_compose.
    - trans (interp_cont K env (Err e)).
      + f_equiv. by apply NATOP_Err_l, interp_val_asval.
      + apply hom_err.
  Qed.

  (* ResetK is not a homomorphism *)
  (* Lemma interp_ectx_reset_not_hom {S} env : *)
  (*   IT_hom (interp_ectx ([ResetK] : ectx S) env) -> False. *)
  (* Proof. *)
  (*   intros [ _ Hi _ _ ]. simpl in Hi. *)
  (*   specialize (Hi (Ret 0)). *)
  (*   unfold interp_reset, CALLCC, CALLCC_ in Hi. *)
  (*   simpl in Hi. *)
  (*   apply bi.siProp.pure_soundness. *)
  (*   iApply IT_tick_vis_ne. *)
  (*   iPureIntro. *)
  (*   symmetry. *)
  (*   eapply Hi. *)
  (*   Unshelve. apply bi.siProp_internal_eq. *)
  (* Qed. *)

  (* #[global] Instance interp_ectx_hom_reset {S} (K : ectx S) *)
  (*   (env : interp_scope S) : *)
  (*   IT_hom (interp_ectx K env) -> *)
  (*   IT_hom (interp_ectx (ResetK :: K) env). *)
  (* Proof. *)
  (*   intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl; unfold interp_reset. *)

  (*   - rewrite -hom_tick. f_equiv. by rewrite get_val_tick. *)
  (*   - rewrite get_val_vis. rewrite hom_vis. f_equiv. *)
  (*     intro. simpl. rewrite -laterO_map_compose. done. *)
  (*   - by rewrite get_val_err hom_err. *)
  (* Qed. *)


  Lemma get_fun_ret' E A `{Cofe A} n : (∀ f, @get_fun E A _ f (core.Ret n) ≡ Err RuntimeErr).
  Proof.
    intros.
    by rewrite IT_rec1_ret.
  Qed.


  #[global] Instance interp_cont_hom {S}
    (K : cont S) env :
    IT_hom (interp_cont K env).
  Proof.
    induction K; simpl; apply _.
  Qed.

  (** ** Finally, preservation of reductions *)
  Lemma interp_expr_head_step {S : Set} (env : interp_scope S) (e : expr S) e' K K' Ko n :
    head_step e K e' K' Ko (n, 0) →
    interp_expr e env ≡ Tick_n n $ interp_expr e' env.
  Proof.
    inversion 1; cbn-[IF APP' Tick get_ret2].
    - (* app lemma *)
      subst.
      erewrite APP_APP'_ITV; last apply _.
      trans (APP (Fun (Next (ir_unf (interp_expr e1) env))) (Next $ interp_val v2 env)).
      { repeat f_equiv. apply interp_rec_unfold. }
      rewrite APP_Fun. simpl. rewrite Tick_eq. do 2 f_equiv.
      simplify_eq.
      rewrite !interp_expr_subst.
      f_equiv.
      intros [| [| x]]; simpl; [| reflexivity | reflexivity].
      rewrite interp_val_ren.
      f_equiv.
      intros ?; simpl; reflexivity.
    - (* continuations *)
      subst.
      erewrite APP_APP'_ITV; last apply _.
      rewrite APP_Fun. simpl. rewrite -Tick_eq. do 2 f_equiv.
      rewrite interp_expr_subst.
      f_equiv.
      intros [|?]; eauto.
    - (* the natop stuff *)
      simplify_eq.
      destruct v1,v2; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
    - rewrite IF_True; last lia.
      reflexivity.
    - rewrite IF_False; last lia.
      reflexivity.
  Qed.

  Lemma interp_expr_fill_no_reify {S} (env : interp_scope S) (e e' : expr S) n :
    prim_step e e' (n, 0) →
    interp_expr e env ≡ Tick_n n $ interp_expr e' env.
  Proof.
    inversion 1; subst.
    inversion H1; subst; rewrite !interp_comp; simpl.
    - rewrite -hom_tick. rewrite -(shift_context_app K Ki' Ko); eauto.
      f_equiv. eapply (interp_expr_head_step env _ _ _ _ _) in H1.
      simpl in H1. done.
    - rewrite -!hom_tick. rewrite -(shift_context_app K Ki' Ko); eauto.
      f_equiv. eapply (interp_expr_head_step env _ _ _ _ _) in H1.
      simpl in H1. done.
    - rewrite -(shift_context_app K Ki' Ko); eauto.
      f_equiv. eapply (interp_expr_head_step env _ _ _ _ _) in H1.
      simpl in H1. done.
    - rewrite -(shift_context_app K Ki' Ko); eauto.
      f_equiv. eapply (interp_expr_head_step env _ _ _ _ _) in H1.
      simpl in H1. done.
    - rewrite -(shift_context_app K Ki' Ko); eauto.
      f_equiv. eapply (interp_expr_head_step env _ _ _ _ _) in H1.
      simpl in H1. done.
  Qed.

  Opaque extend_scope.
  Opaque Ret.



  Parameter env : @interp_scope F R CR ∅.
  Parameter σ : state.
  Parameter (σr : gState_rest sR_idx rs ♯ IT).
  Example term : expr ∅ := ((#2) + reset ((#3) + shift/cc (rec (($0) ⋆ (# 5)))))%syn.
  (* Goal forall e, (interp_expr term env) ≡ e -> *)
  (*   exists e' σ', reify (gReifiers_sReifier rs) *)
  (*               e (gState_recomp σr (sR_state σ)) ≡ (gState_recomp σr (sR_state σ'), e'). *)
  (* Proof. *)
  (*   intros. *)
  (*   eexists. eexists. Opaque CALLCC_. simpl in H. *)
  (*   rewrite /interp_reset in H. *)
  (*   rewrite !hom_CALLCC_ in H. *)
  (*   match goal with *)
  (*   | H : (equiv ?f e) |- _ => set (g := f) *)
  (*   end. *)
  (*   trans (reify (gReifiers_sReifier rs) g (gState_recomp σr (sR_state σ))). *)
  (*   { f_equiv. f_equiv. symmetry. apply H. } *)
  (*   subst g. *)
  (*   rewrite reify_vis_eq //; first last. *)
  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ (sReifier_re _ _) (?f, _, ?h)] => set (i := f); set (o := h) *)
  (*   end. *)
  (*   epose proof (@subReifier_reify sz reify_delim rs _ IT _ op_callcc (subEff_ins^-1 i) _ (o ◎ subEff_outs) σ _ σr) as He. *)
  (*   simpl in He |-*. *)
  (*   erewrite <-He; last reflexivity. *)
  (*   f_equiv. *)
  (*   - intros [][][]. simpl. solve_proper. *)
  (*   - f_equiv. f_equiv. *)
  (*     + f_equiv. by rewrite ofe_iso_21. *)
  (*     + intro. simpl. rewrite ofe_iso_12. done. *)


  Lemma interp_expr_fill_yes_reify {S} K K' Ko env (e e' : expr S)
    (σ σ' : state)
    (σr : gState_rest sR_idx rs ♯ IT) n :
    head_step e K e' K' Ko (n, 1) →
    some_relation K Ko σ ->
    some_relation K' Ko σ ->
    reify (gReifiers_sReifier rs)
      (interp_expr (fill K e) env) (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K' e') env).
  Proof.
    intros Hst H1. apply (interp_ectx_hom K env) in H1.
    trans (reify (gReifiers_sReifier rs) (interp_ectx K env (interp_expr e env))
             (gState_recomp σr (sR_state σ))).
    { f_equiv. by rewrite interp_comp. }
    inversion Hst; simplify_eq; cbn-[gState_recomp].
    - trans (reify (gReifiers_sReifier rs) (INPUT (interp_ectx K' env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv; eauto.
        rewrite hom_INPUT.
        do 2 f_equiv. by intro.
      }
      rewrite reify_vis_eq //; first last.
      {
        epose proof (@subReifier_reify sz reify_io rs _ IT _ (inl ()) () (Next (interp_ectx K' env (Ret n0))) (NextO ◎ (interp_ectx K' env ◎ Ret)) σ σ' σr) as H.
        simpl in H.
        simpl.
        erewrite <-H; last first.
        - rewrite H8. reflexivity.
        - f_equiv;
          solve_proper.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
    - trans (reify (gReifiers_sReifier rs) (interp_ectx K' env (OUTPUT n0)) (gState_recomp σr (sR_state σ))).
      {
        do 3 f_equiv; eauto.
        rewrite get_ret_ret//.
      }
      trans (reify (gReifiers_sReifier rs) (OUTPUT_ n0 (interp_ectx K' env (Ret 0))) (gState_recomp σr (sR_state σ))).
      {
        do 2 f_equiv; eauto.
        by rewrite hom_OUTPUT_.
      }
      rewrite reify_vis_eq //; last first.
      {
        epose proof (@subReifier_reify sz reify_io rs _ IT _ op_output
                       n0 (Next (interp_ectx K' env ((Ret 0))))
                       (constO (Next (interp_ectx K' env ((Ret 0)))))
                       σ (update_output n0 σ) σr) as H.
        simpl in H.
        simpl.
        erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. by rewrite /prod_map H0.
        + do 2 f_equiv. by intro.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
    - match goal with
      | |- context G
             [(ofe_mor_car _ _ (get_fun (?g))
                 ?e)] => set (f := g)
      end.
      match goal with
      | |- context G [(?s, _)] => set (gσ := s) end.
      (* Transparent SHIFT. *)
      (* unfold SHIFT. *)
      set (subEff1 := @subReifier_subEff sz reify_io rs subR).
      trans (reify (gReifiers_sReifier rs)
               (interp_ectx' K env
                  (get_fun f (Fun (Next (ir_unf (interp_expr e0) env))))) gσ).
      { repeat f_equiv. apply interp_rec_unfold. }
      trans (reify (gReifiers_sReifier rs)
               (interp_ectx K env
                  (f (Next (ir_unf (interp_expr e0) env)))) gσ).
      { repeat f_equiv. apply get_fun_fun. }
      subst f.
      Opaque interp_ectx.
      simpl.
      match goal with
      | |- context G [(ofe_mor_car _ _ SHIFT ?g)] => set (f := g)
      end.
      trans (reify (gReifiers_sReifier rs)
               (SHIFT_ f (laterO_map (λne y, interp_ectx K env y) ◎ idfun)) gσ).
      {
        do 2 f_equiv.
        rewrite -(@hom_SHIFT_ F R CR subEff1 idfun f _).
        by f_equiv.
      }
      rewrite reify_vis_eq//; last first.
      {
        simpl.
        epose proof (@subReifier_reify sz reify_io rs subR IT _
                       op_shift f _
                       (laterO_map (interp_ectx K env)) σ' σ' σr) as H.
        simpl in H.
        erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. by rewrite /prod_map H2.
        + do 3f_equiv; try done. by intro.
      }
      clear f.
      f_equiv.
      rewrite -Tick_eq. f_equiv.
      rewrite !interp_expr_subst. f_equiv.
      intros [|[|x]]; eauto. simpl.
      Transparent extend_scope.
      simpl. repeat f_equiv. intro. simpl.
      rewrite laterO_map_Next -Tick_eq. f_equiv.
      rewrite interp_expr_ren interp_comp. simpl.
      symmetry.
      etrans; first by apply interp_ectx_ren.
      repeat f_equiv. unfold ren_scope. simpl. by intro.
      (* rewrite APP'_Fun_r. *)
      (* match goal with *)
      (* | |- context G [(ofe_mor_car _ _ (ofe_mor_car _ _ APP _) ?f)] => *)
      (*     trans (APP (Fun $ Next $ ir_unf (interp_expr e0) env) f); last first *)
      (* end. *)
      (* { repeat f_equiv; try by rewrite interp_rec_unfold. } *)
      (* rewrite APP_Fun -!Tick_eq. simpl. *)
      (* repeat f_equiv. *)
      (* intro. simpl. *)
      (* rewrite interp_comp laterO_map_Next -Tick_eq. f_equiv. *)
      (* symmetry. *)
      (* Transparent extend_scope. *)
      (* fold (@interp_ectx S K env). *)
      (* Opaque interp_ectx. *)
      (* simpl. *)
      (* etrans; first by apply interp_ectx_ren. *)
      (* repeat f_equiv. *)
      (* unfold ren_scope. simpl. *)
      (* apply ofe_mor_ext. done. *)
      (* Transparent interp_ectx. *)
      (* Opaque extend_scope. *)
    - Transparent RESET. unfold RESET.
      trans (reify (gReifiers_sReifier rs)
               (RESET_ (laterO_map (λne y, interp_ectx' K' env y) ◎
                          (laterO_map (λne y, get_val idfun y)) ◎
                          idfun)
                  (Next (interp_val v env)))
            (gState_recomp σr (sR_state σ'))).
      {
        do 2 f_equiv; last done.
        rewrite !hom_vis. simpl. f_equiv.
        by intro x.
      }
      rewrite reify_vis_eq//; last first.
      {
        simpl.
        epose proof (@subReifier_reify sz reify_io rs subR IT _
                       op_reset (Next (interp_val v env)) _
                       (laterO_map (interp_ectx K' env) ◎
                                   laterO_map (get_val idfun)) σ' σ' σr) as H.
        simpl in H. erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. by rewrite /prod_map H0.
        + do 2 f_equiv. by intro x.
      }
      f_equiv.
      rewrite laterO_map_Next -Tick_eq. f_equiv.
      rewrite interp_comp. f_equiv.
      simpl. by rewrite get_val_ITV.
  Qed.


  (* Lemma soundness_Ectx {S} (e1 e2 e'1 e'2 : expr S) σ1 σ2 (K1 K2 : ectx S) *)
  (*   (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) : *)
  (*   ResetK ∉ K1 -> *)
  (*   e1 = (K1 ⟪ e'1 ⟫)%syn -> *)
  (*   e2 = (K2 ⟪ e'2 ⟫)%syn -> *)
  (*   head_step e'1 σ1 K1 e'2 σ2 K2 (n, m) -> *)
  (*   ssteps (gReifiers_sReifier rs) *)
  (*     (interp_expr e1 env) (gState_recomp σr (sR_state σ1)) *)
  (*     (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n. *)
  (* Proof. *)
  (*   Opaque gState_decomp gState_recomp. *)
  (*   intros. simplify_eq/=. *)
  (*     destruct (head_step_io_01 _ _ _ _ _ _ _ _ H2); subst. *)
  (*     - assert (σ1 = σ2) as ->. *)
  (*       { eapply head_step_no_io; eauto. } *)
  (*       unshelve eapply (interp_expr_fill_no_reify K1) in H2; first apply env; last apply H. *)
  (*       rewrite H2. *)
  (*       rewrite interp_comp. *)
  (*       eapply ssteps_tick_n. *)
  (*     - specialize (interp_ectx_hom K1 env H) as Hhom. *)
  (*       inversion H2;subst. *)
  (*       + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr) in H2; last apply H. *)
  (*         rewrite interp_comp. simpl. *)
  (*         rewrite hom_INPUT. *)
  (*         change 1 with (Nat.add 1 0). econstructor; last first. *)
  (*         { apply ssteps_zero; reflexivity. } *)
  (*         eapply sstep_reify. *)
  (*         { Transparent INPUT. unfold INPUT. simpl. *)
  (*           f_equiv. reflexivity. } *)
  (*         simpl in H2. *)
  (*         rewrite -H2. *)
  (*         repeat f_equiv; eauto. *)
  (*         rewrite interp_comp hom_INPUT. *)
  (*         eauto. *)
  (*       + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H. *)
  (*         rewrite interp_comp. simpl. *)
  (*         rewrite get_ret_ret. *)
  (*         rewrite hom_OUTPUT_. *)
  (*         change 1 with (Nat.add 1 0). econstructor; last first. *)
  (*         { apply ssteps_zero; reflexivity. } *)
  (*         eapply sstep_reify. *)
  (*         { Transparent OUTPUT_. unfold OUTPUT_. simpl. *)
  (*           f_equiv. reflexivity. } *)
  (*         simpl in H. *)
  (*         rewrite -H. *)
  (*         repeat f_equiv; eauto. *)
  (*         Opaque OUTPUT_. *)
  (*         rewrite interp_comp /= get_ret_ret hom_OUTPUT_. *)
  (*         eauto. *)
  (*       + eapply (interp_expr_fill_yes_reify K1 [] env _ _ _ _ σr _ H2) in H. *)
  (*         rewrite !interp_comp. *)
  (*         Opaque interp_ectx. simpl. *)
  (*         match goal with *)
  (*         | |- context G [ofe_mor_car _ _ (get_fun _) ?g] => set (f := g) *)
  (*         end. *)
  (*         assert (f ≡ Fun $ Next $ ir_unf (interp_expr e) env) as -> by apply interp_rec_unfold. *)
  (*         rewrite get_fun_fun. *)
  (*         simpl. *)
  (*         econstructor; last constructor; last done; last done. *)
  (*         eapply sstep_reify. *)
  (*         { rewrite hom_SHIFT_. simpl. *)
  (*           f_equiv. reflexivity. } *)
  (*         simpl in H. rewrite -H. repeat f_equiv. *)
  (*         rewrite interp_comp. f_equiv. simpl. *)
  (*         match goal with *)
  (*           |- context G [ ofe_mor_car _ _ (get_fun ?g)] => set (gi := g) *)
  (*           end. *)
  (*         trans (get_fun gi *)
  (*                  (Fun $ Next $ ir_unf (interp_expr e) env)); last by rewrite interp_rec_unfold. *)
  (*         rewrite get_fun_fun. simpl. reflexivity. *)
  (*       + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H. *)
  (*         rewrite !interp_comp.  *)
  (*         econstructor; last constructor; last done; last done. *)
  (*         eapply sstep_reify. *)
  (*         { simpl. rewrite !hom_vis. reflexivity. } *)
  (*         simpl in H2. *)
  (*         trans (gState_recomp σr (sR_state σ2), *)
  (*                  Tick (interp_expr (K2 ⟪ v ⟫)%syn env)); *)
  (*           last by (repeat f_equiv; apply interp_comp). *)
  (*         rewrite -H. repeat f_equiv. by rewrite interp_comp. *)
  (* Qed. *)

  Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) :
    prim_step e1 σ1 e2 σ2 (n,m) →
    ssteps (gReifiers_sReifier rs)
              (interp_expr e1 env) (gState_recomp σr (sR_state σ1))
              (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n.
  Proof.
    Opaque gState_decomp gState_recomp.
    inversion 1; simplify_eq/=.
    rewrite !interp_comp.
    pose proof (shift_context_no_reset K Ki Ko H0).
    destruct (head_step_io_01 _ _ _ _ _ _ _ _ _ H1); subst.
      - assert (σ1 = σ2) as ->.
        { eapply head_step_no_io; eauto. }
        unshelve eapply (interp_expr_fill_no_reify Ki) in H1; first apply env; last apply H2.
        rewrite H1.
        rewrite interp_comp.
        eapply ssteps_tick_n.
      - specialize (interp_ectx_hom K1 env H) as Hhom.
        inversion H2;subst.
        + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr) in H2; last apply H.
          rewrite interp_comp. simpl.
          rewrite hom_INPUT.
          change 1 with (Nat.add 1 0). econstructor; last first.
          { apply ssteps_zero; reflexivity. }
          eapply sstep_reify.
          { Transparent INPUT. unfold INPUT. simpl.
            f_equiv. reflexivity. }
          simpl in H2.
          rewrite -H2.
          repeat f_equiv; eauto.
          rewrite interp_comp hom_INPUT.
          eauto.
        + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H.
          rewrite interp_comp. simpl.
          rewrite get_ret_ret.
          rewrite hom_OUTPUT_.
          change 1 with (Nat.add 1 0). econstructor; last first.
          { apply ssteps_zero; reflexivity. }
          eapply sstep_reify.
          { Transparent OUTPUT_. unfold OUTPUT_. simpl.
            f_equiv. reflexivity. }
          simpl in H.
          rewrite -H.
          repeat f_equiv; eauto.
          Opaque OUTPUT_.
          rewrite interp_comp /= get_ret_ret hom_OUTPUT_.
          eauto.
        + eapply (interp_expr_fill_yes_reify K1 [] env _ _ _ _ σr _ H2) in H.
          rewrite !interp_comp.
          Opaque interp_ectx. simpl.
          match goal with
          | |- context G [ofe_mor_car _ _ (get_fun _) ?g] => set (f := g)
          end.
          assert (f ≡ Fun $ Next $ ir_unf (interp_expr e) env) as -> by apply interp_rec_unfold.
          rewrite get_fun_fun.
          simpl.
          econstructor; last constructor; last done; last done.
          eapply sstep_reify.
          { rewrite hom_SHIFT_. simpl.
            f_equiv. reflexivity. }
          simpl in H. rewrite -H. repeat f_equiv.
          rewrite interp_comp. f_equiv. simpl.
          match goal with
            |- context G [ ofe_mor_car _ _ (get_fun ?g)] => set (gi := g)
            end.
          trans (get_fun gi
                   (Fun $ Next $ ir_unf (interp_expr e) env)); last by rewrite interp_rec_unfold.
          rewrite get_fun_fun. simpl. reflexivity.
        + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H.
          rewrite !interp_comp.
          econstructor; last constructor; last done; last done.
          eapply sstep_reify.
          { simpl. rewrite !hom_vis. reflexivity. }
          simpl in H2.
          trans (gState_recomp σr (sR_state σ2),
                   Tick (interp_expr (K2 ⟪ v ⟫)%syn env));
            last by (repeat f_equiv; apply interp_comp).
          rewrite -H. repeat f_equiv. by rewrite interp_comp.




  (*   unshelve epose proof (soundness_Ectx (Ki ⟪ e0 ⟫)%syn (Ki' ⟪ e3 ⟫)%syn e0 e3 σ1 σ2 Ki Ki' σr n m env H2 _ _ H1 ); try done. *)
  (*   pose proof (shift_context_app K Ki Ko H0) as ->. *)
  (*   pose proof (interp_val_asval v (D := env)). *)
  (*   rewrite get_val_ITV. *)
  (*   simpl. *)
  (*   rewrite get_fun_fun. *)
  (*   simpl. *)
  (*   change 2 with (Nat.add (Nat.add 1 1) 0). *)
  (*   econstructor; last first. *)
  (*   { apply ssteps_tick_n. } *)
  (*   eapply sstep_reify; first (rewrite hom_vis; reflexivity). *)
  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ _ (Next ?f)] => set (f' := f) *)
  (*   end. *)
  (*   trans (reify (gReifiers_sReifier rs) (THROW (interp_val v env) (Next f')) (gState_recomp σr (sR_state σ2))). *)
  (*   { *)
  (*     f_equiv; last done. *)
  (*     f_equiv. *)
  (*     rewrite hom_vis. *)
  (*     Transparent THROW. *)
  (*     unfold THROW. *)
  (*     simpl. *)
  (*     repeat f_equiv. *)
  (*     intros x; simpl. *)
  (*     destruct ((subEff_outs ^-1) x). *)
  (*   } *)
  (*   rewrite reify_vis_eq; first (rewrite Tick_eq; reflexivity). *)
  (*   simpl. *)
  (*   match goal with *)
  (*   | |- context G [(_, _, ?a)] => set (κ := a) *)
  (*   end. *)
  (*   epose proof (@subReifier_reify sz reify_io rs subR IT _ *)
  (*                  (inr (inr (inr (inl ())))) (Next (interp_val v env), Next f') *)
  (*                  (Next (Tau (Next ((interp_ectx K' env) (interp_val v env))))) *)
  (*                  (Empty_setO_rec _) σ2 σ2 σr) as H'. *)
  (*   subst κ. *)
  (*   simpl in H'. *)
  (*   erewrite <-H'; last reflexivity. *)
  (*   rewrite /prod_map. *)
  (*   f_equiv; first solve_proper. *)
  (*   do 2 f_equiv; first reflexivity. *)
  (*   intro; simpl. *)
  (*   f_equiv. *)
  (*   } *)
  (* Qed. *)

End interp.
#[global] Opaque INPUT OUTPUT_ CALLCC THROW.
