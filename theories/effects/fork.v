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

  Lemma wp_fork (σ : stateO) (n : IT) (k : IT -n> IT) `{!IT_hom k} Φ s :
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} (k (Ret ())) @ s {{ Φ }}
                                 ∗ ▷ WP@{rs} n @ s {{ fork_post }}) -∗
    WP@{rs} k (FORK n) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold FORK. simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iModIntro.
    iExists σ, (), σ, (k (Ret ())), [NextO n].
    iFrame "Hs".
    iSplit; first done.
    rewrite /= ofe_iso_21 later_map_Next.
    iSplit; first done.
    iNext.
    iIntros "Hc Hs !>".
    iDestruct ("Ha" with "Hc Hs") as "(Ha1 & Ha2)".
    iSplitL "Ha1"; first done.
    rewrite /weakestpre.wptp big_sepL2_singleton.
    rewrite -Tick_eq.
    iApply wp_tick.
    by iNext; iIntros "_".
  Qed.

End weakestpre.
