(** * I/O on a tape effect *)
From gitrees Require Import prelude gitree.
Require Import iris.algebra.list.

Record state := State {
                   inputs : list nat;
                   outputs : list nat;
                 }.
#[export] Instance state_inhabited : Inhabited state := populate (State [] []).

Definition update_input (s : state) : nat * state :=
  match s.(inputs) with
  | [] => (0, s)
  | n::ns =>
      (n, {| inputs := ns; outputs := s.(outputs) |})
  end.
Definition update_output (n:nat) (s : state) : state :=
  {| inputs := s.(inputs); outputs := n::s.(outputs) |}.

Notation stateO := (leibnizO state).

Program Definition inputE : opInterp :=
  {|
    Ins := unitO;
    Outs := natO;
  |}.

Program Definition outputE : opInterp :=
  {|
    Ins := natO;
    Outs := unitO;
  |}.

Definition ioE := @[inputE;outputE].

(* INPUT *)
Definition reify_input X `{Cofe X} : unitO * stateO →
                                      option (natO * stateO * listO (laterO X)) :=
    λ '(o, σ), Some (update_input σ : prodO natO stateO, []).
#[export] Instance reify_input_ne X `{Cofe X} :
  NonExpansive (reify_input X).
Proof.
  intros ?[[]][[]][_?]. simpl in *. f_equiv.
  repeat f_equiv. done.
Qed.

(* OUTPUT *)
Definition reify_output X `{Cofe X} : (natO * stateO) →
                                       option (unitO * stateO * listO (laterO X)) :=
  λ '(n, σ), Some((), update_output n σ : stateO, []).
#[export] Instance reify_output_ne X `{Cofe X} :
  NonExpansive (reify_output X).
Proof.
  intros ?[][][]. simpl in *.
  repeat f_equiv; done.
Qed.

Program Canonical Structure reify_io : sReifier NotCtxDep :=
  Build_sReifier NotCtxDep ioE stateO _ _ _.
Next Obligation.
  intros X HX op.
  destruct op as [[] | [ | []]]; simpl.
  - simple refine (OfeMor (reify_input X)).
  - simple refine (OfeMor (reify_output X)).
Defined.

Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff ioE E}.
  Context {subOfe0 : SubOfe natO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Program Definition INPUT : (nat -n> IT) -n> IT := λne k, Vis (E:=E) (subEff_opid (inl ()))
                                                             (subEff_ins (F:=ioE) (op:=(inl ())) ())
                                                             (NextO ◎ k ◎ (subEff_outs (F:=ioE) (op:=(inl ())))^-1).
  Solve Obligations with solve_proper.
  Program Definition OUTPUT_ : nat -n> IT -n> IT :=
    λne m α, Vis (E:=E) (subEff_opid (inr (inl ())))
                        (subEff_ins (F:=ioE) (op:=(inr (inl ()))) m)
                        (λne _, NextO α).
  Solve All Obligations with solve_proper_please.
  Program Definition OUTPUT : nat -n> IT := λne m, OUTPUT_ m (Ret 0).

  Lemma hom_INPUT k f `{!IT_hom f} : f (INPUT k) ≡ INPUT (OfeMor f ◎ k).
  Proof.
    unfold INPUT.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map]. rewrite laterO_map_Next.
    done.
  Qed.
  Lemma hom_OUTPUT_ m α f `{!IT_hom f} : f (OUTPUT_ m α) ≡ OUTPUT_ m (f α).
  Proof.
    unfold OUTPUT.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map]. rewrite laterO_map_Next.
    done.
  Qed.

End constructors.

Section weakestpre.
  Context {sz : nat}.
  Context {a : is_ctx_dep}.
  Variable (rs : gReifiers a sz).
  Context {subR : subReifier (sReifier_NotCtxDep_min reify_io a) rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_input (σ σ' : stateO) (n : nat) (k : natO -n> IT) Φ s :
    update_input σ = (n, σ') →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} (k n) @ s {{ Φ }}) -∗
    WP@{rs} (INPUT k) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold INPUT. simpl.
    iApply wp_subreify_ctx_indep_lift''.
    iModIntro.
    iExists σ, n, σ', (k n), [].
    iFrame "Hs".
    iSplit; first by rewrite -Hs.
    iSplit; first by (simpl; rewrite ofe_iso_21).
    iNext.
    iIntros "Hc Hs !>".
    iSimpl. rewrite /wptp big_sepL2_nil.
    iSplitR ""; last done.
    iApply ("Ha" with "Hc Hs").
  Qed.

  Lemma wp_output_ (σ σ' : stateO) (n : nat) α Φ s :
    update_output n σ = σ' →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} α @ s {{ Φ }}) -∗
    WP@{rs} (OUTPUT_ n α) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold OUTPUT. simpl.
    iApply wp_subreify_ctx_indep_lift''.
    iModIntro.
    iExists σ, (), σ', α, [].
    simpl.
    iFrame "Hs".
    iSplit; first by rewrite -Hs.
    iSplit; first done.
    iNext.
    iIntros "H1 H2".
    iModIntro.
    iSimpl. rewrite /wptp big_sepL2_nil.
    iSplitR ""; last done.
    by iApply ("Ha" with "H1 H2").
  Qed.

  Lemma wp_output (σ σ' : stateO) (n : nat) Φ s :
    update_output n σ = σ' →
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ' -∗ Φ (RetV 0))
    -∗ WP@{rs} (OUTPUT n) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold OUTPUT. cbn [ofe_mor_car].
    iApply (wp_output_ with "Hs"); first done.
    iNext.
    iIntros "Hc Hs".
    iApply wp_val.
    iModIntro.
    iApply ("Ha" with "Hc Hs").
  Qed.

End weakestpre.

Section weakestpre.
  Context {sz : nat}.
  Context {a : is_ctx_dep}.
  Variable (rs : gReifiers a sz).
  Context {subR : subReifier (sReifier_NotCtxDep_min reify_io a) rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Program Definition io_ctx :=
    inv (nroot.@"ioE")
      (∃ σ, £ 1 ∗ has_substate σ)%I.

  Lemma wp_input_agnostic (k : natO -n> IT) Φ s :
    io_ctx
    -∗ ▷ (∀ n, WP@{rs} (k n) @ s {{ Φ }})
    -∗ WP@{rs} (INPUT k) @ s {{ Φ }}.
  Proof.
    iIntros "#Hs Ha".
    unfold INPUT. simpl.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"ioE") as (σ) "[>Hcr Hb]" "Hcl".
    iApply (fupd_mask_weaken (⊤ ∖ ↑nroot.@"ioE")).
    { set_solver. }
    iIntros "Hwk".
    iApply (lc_fupd_elim_later with "Hcr").
    iNext. simpl in σ.
    destruct σ as [[|n i] o].
    - iExists (State [] o), 0, (State [] o), (k 0), [].
      iFrame "Hb".
      iSplit; first done.
      rewrite /= ofe_iso_21.
      iSplit; first done.
      iNext.
      iIntros "Hcr".
      iIntros "HS".
      iSpecialize ("Ha" $! 0).
      iFrame "Ha".
      rewrite /weakestpre.wptp big_sepL2_nil.
      iSpecialize ("Hcl" with "[$Hcr HS]").
      + iNext. iExists _. iFrame "HS".
      + iApply (fupd_mono with "Hcl").
        by iIntros "_".
    - iExists (State (n :: i) o), n, (State i o), (k n), [].
      iFrame "Hb".
      iSplit; first done.
      rewrite /= ofe_iso_21.
      iSplit; first done.
      iNext.
      iIntros "Hcr".
      iIntros "HS".
      iSpecialize ("Ha" $! n).
      iFrame "Ha".
      rewrite /weakestpre.wptp big_sepL2_nil.
      iSpecialize ("Hcl" with "[$Hcr HS]").
      + iNext. iExists _. iFrame "HS".
      + iApply (fupd_mono with "Hcl").
        by iIntros "_".
  Qed.

  Lemma wp_output_agnostic (n : nat) Φ s :
    io_ctx
    -∗ ▷ (Φ (RetV 0))
    -∗ WP@{rs} (OUTPUT n) @ s {{ Φ }}.
  Proof.
    iIntros "#Hs Ha".
    unfold OUTPUT. simpl.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"ioE") as (σ) "[>Hcr Hb]" "Hcl".
    iApply (fupd_mask_weaken (⊤ ∖ ↑nroot.@"ioE")).
    { set_solver. }
    iIntros "Hwk".
    iApply (lc_fupd_elim_later with "Hcr").
    iNext. simpl in σ.
    destruct σ as [i o].
    iExists (State i o), (), (State i (n :: o)), (Ret 0), [].
    iFrame "Hb".
    iSplit; first done.
    iSplit; first done.
    iNext.
    iIntros "Hcr".
    iIntros "HS".
    rewrite /weakestpre.wptp big_sepL2_nil.
    iAssert emp%I as "H"; last iFrame "H"; first done.
    iApply wp_val.
    iFrame "Ha".
    iSpecialize ("Hcl" with "[$Hcr HS]").
    + iNext. iExists _. iFrame "HS".
    + iApply (fupd_mono with "Hcl").
      by iIntros "_".
  Qed.

End weakestpre.
