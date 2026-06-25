From iris.prelude Require Import options.
From iris.base_logic Require Import base_logic.
From gitrees Require Import prelude hom greifiers.
From gitrees.gitree Require Import core subofe reify.
From gitrees.effects Require Import prng.

Section get_ret2_generalized.
  Local Opaque laterO_ap.
  Context {Σ : opsInterp}.
  Context `{!Cofe A, !Cofe B, !Cofe R}.
  Context `{!SubOfe A R, !SubOfe B R}.
  Notation IT := (IT Σ R).

  Program Definition get_ret2 (f : A -n> B -n> IT) : IT -n> IT -n> IT := λne x y,
    get_ret (λne x, get_ret (λne y, f x y) y) x.
  Solve All Obligations with solve_proper_please.
  Global Instance get_ret2_ne n : Proper ((dist n) ==> (dist n)) get_ret2.
  Proof.
    intros f1 f2 Hf. unfold get_ret2.
    intros x y. simpl. apply get_ret_ne.
    clear x. intros x. simpl. apply get_ret_ne.
    clear y. intros y. simpl. apply Hf.
  Qed.
  Global Instance get_ret2_proper : Proper ((≡) ==> (≡)) get_ret2.
  Proof.
    intros f1 f2 Hf. unfold get_ret2.
    intros x y. simpl. apply get_ret_proper.
    clear x. intros x. simpl. apply get_ret_proper.
    clear y. intros y. simpl. apply Hf.
  Qed.
End get_ret2_generalized.

Section prng_seed_workaround.
  Context {Rng : Prng nat nat}.
  Context {sz : nat}.
  Locate NotCtxDep.
  Variable (rs : gReifiers NotCtxDep sz).
  Context {subR : subReifier (reify_prng Rng) rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R} `{!SubOfe locO R} `{!SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Program Definition SeedGit_ne : IT -n> IT -n> IT := λne tloc tseed,
      get_val (λne vloc,
        get_val (λne vseed,
                   get_ret2 PRNG_SEED vloc vseed) tseed) tloc.
  Solve All Obligations with solve_proper_please.
  Definition SeedGit tloc tseed := SeedGit_ne tloc tseed.
  Global Instance SEEDOP_Proper
    : Proper ((≡) ==> (≡) ==> (≡)) (SeedGit).
  Proof. rewrite /SeedGit; solve_proper_please. Qed.
  Global Instance SeedGit_NonExp : NonExpansive2 (SeedGit).
  Proof. rewrite /SeedGit; solve_proper_please. Qed.

  Lemma SeedGit_ErrS β e : AsVal β → SeedGit β (Err e) ≡ Err e.
  Proof.
    intros ?. simpl.
    rewrite /SeedGit /SeedGit_ne //= get_val_ITV /= get_val_err //.
  Qed.
  Lemma SeedGit_ErrL e tseed : SeedGit (Err e) tseed ≡ Err e.
  Proof. simpl. by rewrite /SeedGit /SeedGit_ne //= get_val_err. Qed.
  Lemma SeedGit_Ret loc seed :
    SeedGit (Ret loc) (Ret seed) ≡ PRNG_SEED loc seed.
  Proof.
    simpl.
    rewrite /SeedGit /SeedGit_ne /= get_val_ret/= get_val_ret/=.
    rewrite !get_ret_ret. simpl.
    rewrite !get_ret_ret. simpl.
    done.
  Qed.
  Lemma SeedGit_TickL tloc tseed:
    SeedGit (Tick tloc) tseed  ≡ Tick $ SeedGit tloc tseed.
  Proof.
    simpl. rewrite /SeedGit /SeedGit_ne /= get_val_tick//.
  Qed.
  Lemma SeedGit_TickL_n tloc tseed n :
    SeedGit (Tick_n n tloc) tseed ≡ Tick_n n $ SeedGit tloc tseed.
  Proof.
    induction n; eauto. rewrite SeedGit_TickL.
    rewrite IHn. done.
  Qed.
  Lemma SeedGit_ITV_TickS tseed β :
    AsVal β →
    SeedGit β (Tick tseed) ≡ Tick $ SeedGit β tseed.
  Proof.
    intros ?. simpl. rewrite /SeedGit /SeedGit_ne /= get_val_ITV/=.
    rewrite get_val_tick. f_equiv.
    rewrite get_val_ITV. done.
  Qed.
  Lemma SeedGit_ITV_TickS_n tseed β n :
    AsVal β →
    SeedGit β (Tick_n n tseed) ≡ Tick_n n $ SeedGit β tseed.
  Proof.
    intros Hb.
    induction n; eauto. rewrite SeedGit_ITV_TickS.
    rewrite IHn. done.
  Qed.
  Lemma SeedGit_ITV_VisS op i k β :
    AsVal β →
    SeedGit β (Vis op i k) ≡
    Vis op i (laterO_map (SeedGit_ne β) ◎ k).
  Proof.
    intros ?. simpl. rewrite /SeedGit /SeedGit_ne /= get_val_ITV/=.
    rewrite get_val_vis. repeat f_equiv.
    intro y. simpl. rewrite get_val_ITV//.
  Qed.
  Lemma SeedGit_VisL tseed op i k :
    SeedGit (Vis op i k) tseed ≡ Vis op i (laterO_map (flipO SeedGit_ne tseed) ◎ k).
  Proof.
    simpl. rewrite /SeedGit /SeedGit_ne /= get_val_vis. f_equiv. solve_proper.
  Qed.

  Opaque SeedGit.
  Definition SeedGitCtxL β holeL := SeedGit holeL β.
  Definition SeedGitCtxS βval holeS := SeedGit βval holeS.

  #[local] Instance SeedGitCtxL_ne (β : IT) : NonExpansive (SeedGitCtxL β).
  Proof.
    intro n. unfold SeedGitCtxL.
    repeat intro. repeat f_equiv; eauto.
  Qed.
  #[local] Instance SeedGitCtxS_ne (β : IT) : NonExpansive (SeedGitCtxS β).
  Proof.
    intro n. unfold SeedGitCtxS.
    solve_proper.
  Qed.
  #[export] Instance SeedGitCtxS_hom (β : IT) `{!AsVal β} : IT_hom (SeedGitCtxS β).
  Proof.
    unfold SeedGitCtxS.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite SeedGit_ITV_TickS//.
    - intros op' i k. simpl. rewrite SeedGit_ITV_VisS//.
      repeat f_equiv. intro. reflexivity.
    - intros e. simpl. rewrite SeedGit_ErrS//.
  Qed.
  #[export] Instance SeedGitCtxL_hom (β : IT) : IT_hom (SeedGitCtxL β).
  Proof.
    unfold SeedGitCtxL.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite SeedGit_TickL//.
    - intros op' i k. simpl. rewrite SeedGit_VisL//.
      repeat f_equiv. intro. reflexivity.
    - intros e. simpl. rewrite SeedGit_ErrL//.
  Qed.
End prng_seed_workaround.

#[global] Opaque SeedGit.
