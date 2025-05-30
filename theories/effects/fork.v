From gitrees Require Import prelude gitree.
Require Import iris.algebra.list.

Definition state := unitO.
#[export] Instance state_inhabited : Inhabited state := populate ().

Notation stateO := (leibnizO state).

Program Definition forkI : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := unitO;
  |}.

Definition concE := @[forkI].

(* FORK *)
Definition reify_fork' X `{Cofe X} : (laterO X) * stateO →
                                      option (unitO * stateO * listO (laterO X)) :=
    λ '(o, σ), Some ((), σ, [o]).
#[export] Instance reify_fork'_ne X `{Cofe X} :
  NonExpansive (reify_fork' X).
Proof.
  intros ?[? []] [? []] G.
  simpl in *. f_equiv.
  do 2 f_equiv.
  apply G.
Qed.

Canonical Structure reify_fork : sReifier NotCtxDep.
Proof.
  simple refine {| sReifier_ops := concE;
                   sReifier_state := stateO
                |}.
  intros X HX op.
  destruct op as [? | []]; simpl.
  simple refine (OfeMor (reify_fork' X)).
Defined.

Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff concE E}.
  Context {subOfe0 : SubOfe unitO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Program Definition FORK : IT -n> IT :=
    λne k, Vis (E:=E) (subEff_opid (inl ()))
             (subEff_ins (F:=concE) (op:=(inl ())) (Next k))
             (NextO ◎ Ret ◎ (subEff_outs (F:=concE) (op:=(inl ())))^-1).
  Solve Obligations with solve_proper.
End constructors.

Section weakestpre.
  Context {sz : nat}.
  Context {a : is_ctx_dep}.
  Variable (rs : gReifiers a sz).
  Context {subR : subReifier (sReifier_NotCtxDep_min reify_fork a) rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Program Definition fork_ctx :=
    inv (nroot.@"forkE")
      (£1 ∗ has_substate ())%I.

  Lemma wp_fork_hom (n : IT) (k : IT -n> IT) `{!IT_hom k} Φ s :
    fork_ctx
    -∗ ▷ WP@{rs} n @ s {{ fork_post }}
    -∗ ▷ WP@{rs} (k (Ret ())) @ s {{ Φ }}
    -∗ WP@{rs} k (FORK n) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha1 Ha2".
    unfold FORK. simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"forkE") as "[>Hcr Hs]" "Hcl".
    iApply (fupd_mask_weaken (⊤ ∖ ↑nroot.@"forkE")).
    { set_solver. }
    iIntros "Hwk".
    iApply (lc_fupd_elim_later with "Hcr").
    iNext.
    iExists (), (), (), (k (Ret ())), [NextO n].
    iFrame "Hs".
    iSplit; first done.
    rewrite /= ofe_iso_21 later_map_Next.
    iSplit; first done.
    iNext.
    iIntros "Hcr".
    iIntros "HS".
    iFrame "Ha2".
    rewrite /weakestpre.wptp big_sepL2_singleton.
    rewrite -Tick_eq.
    iApply wp_tick.
    iFrame "Ha1".
    iSpecialize ("Hcl" with "[$Hcr $HS]").
    iApply (fupd_mono with "Hcl").
    iIntros "_". iNext. iIntros "_".
    done.
  Qed.

  Lemma wp_fork (n : IT) (Φ : ITV -d> iProp) s :
    fork_ctx
    -∗ ▷ WP@{rs} n @ s {{ fork_post }}
    -∗ ▷ Φ (RetV ())
    -∗ WP@{rs} (FORK n) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha1 Ha2".
    iApply (wp_fork_hom _ idfun with "Hs Ha1").
    iNext. iApply wp_val. by iModIntro.
  Qed.

End weakestpre.
