From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.
From gitrees Require Import prelude.
From gitrees Require Import gitree gitree.lambda.
From gitrees Require Import effects.store effects.coroutines.
From gitrees Require Import lib.while.

Opaque CREATE RESUME YIELD LABEL.

Section lib.
  Context {n : nat}.
  Variable (rs : gReifiers CtxDep n).
  Context {R} {CR : Cofe R}.
  Context `{!SubOfe unitO R, !SubOfe natO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).
  Context `{!subReifier reify_coroutines rs}
    `{!subReifier (sReifier_NotCtxDep_min reify_store CtxDep) rs}.

  Local Definition thunk (α : IT) : IT := λit _, α.
  Opaque laterO_map.
  Local Program Definition rec_pre (body : IT -n> IT -n> IT)
    : laterO IT -n> IT :=
    λne self, Fun $ laterO_map (λne f x, body f x) self.
  Solve All Obligations with solve_proper.
  Local Definition rec body : IT := mmuu (rec_pre body).
  Local Lemma rec_unfold (body : IT -n> IT -n> IT) :
    rec body ≡ Fun $ Next $ body (rec body).
  Proof.
    rewrite /rec {1}mmuu_unfold /rec_pre /= laterO_map_Next /=.
    do 2 f_equiv. intros ?; simpl.
    reflexivity.
  Qed.
  Local Program Definition recV_pre (body : IT -n> IT -n> IT)
    : laterO ITV -n> ITV :=
    λne self, FunV $ laterO_map (λne f x, body f x) (later_map IT_of_V self).
  Solve All Obligations with solve_proper.
  Local Definition recV body : ITV := mmuu (recV_pre body).
  Local Lemma recV_unfold (body : IT -n> IT -n> IT) :
    IT_of_V (recV body) ≡ Fun $ Next $ body (IT_of_V (recV body)).
  Proof.
    rewrite /recV {1}mmuu_unfold /recV_pre /= laterO_map_Next /=.
    do 2 f_equiv. intros ?; simpl.
    reflexivity.
  Qed.
  Local Instance rec_val body : IntoVal (rec body) (recV body).
  Proof.
    rewrite /IntoVal.
    apply bi.siProp.internal_eq_soundness.
    iLöb as "IH".
    iEval (rewrite rec_unfold recV_unfold).
    iApply f_equivI.
    iNext.
    iApply f_equivI.
    iApply "IH".
  Qed.
  Transparent laterO_map.

  Program Definition generator_body (seed : IT) (suc : IT -n> IT) : IT :=
    rec (λne f x, SEQ (YIELD x) (f ⊙ (suc x))) ⊙ seed.
  Solve All Obligations with solve_proper.
  Program Definition generator (seed : IT) (suc : IT -n> IT) : IT :=
    thunk $ generator_body seed suc.

  Context `{!gitreeGS_gen rs R Σ, !coroutinesG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_generator l f g seed `{!AsVal seed} (suc : IT -n> IT)
    k `{!IT_hom k}
    t s Φ `{!NonExpansive Φ} :
    coroutines_ctx rs R
    -∗ stack rs R ((l, later_ap (Next g)) :: t)
    -∗ pointsto _ _ l f
    -∗ ▷ (stack rs R t
          -∗ l ↦ laterO_map ((λne x, k x) ◎ (SEQCtx (generator_body (suc seed) suc)))
          -∗ WP@{rs} g seed @ s {{ Φ }})
    -∗ WP@{rs} k ((generator seed suc) ⊙ (Ret ())) @ s {{ Φ }}.
  Proof.
    iIntros "#Hcoroutines Hstack Hpt H".
    iEval (rewrite /generator APP'_Fun_l /= -Tick_eq hom_tick).
    iApply wp_tick.
    iNext. iIntros "Hlc". iSimpl.
    iEval (rewrite /generator_body rec_unfold APP'_Fun_l /= -Tick_eq hom_tick).
    iApply wp_tick.
    iNext. iIntros "Hlc'". iSimpl.
    match goal with
    | |- context G [SEQ ?a ?b] =>
        set (A := a); set (B := b)
    end.
    assert (k (SEQ A B)
              ≡ ((λne x, k x) ◎ (SEQCtx B)) A) as ->; first done.
    subst A. subst B.
    unshelve iApply (wp_yield_hom with "Hcoroutines Hstack Hpt");
      first apply _.
    iNext. iIntros "Hstack Hpt".
    iApply ("H" with "Hstack [Hpt]").
    iApply (internal_eq_rewrite' with "Hpt"); last done.
    iIntros "?".
    iPureIntro.
    f_equiv. simpl.
    apply equiv_dist.
    intros p. simpl.
    rewrite /later_ap /=.
    intros ?. simpl. reflexivity.
  Qed.

  Lemma wp_generator_hom l f g `{!IT_hom g} seed `{!AsVal seed} (suc : IT -n> IT)
    t s Φ `{!NonExpansive Φ} :
    coroutines_ctx rs R
    -∗ stack rs R t
    -∗ pointsto _ _ l f
    -∗ ▷ (stack rs R t
          -∗ l ↦ laterO_map ((λne x, g x) ◎ (SEQCtx (generator_body (suc seed) suc)))
          -∗ WP@{rs} g seed @ s {{ Φ }})
    -∗ WP@{rs} g (LABEL l ((generator seed suc) ⊙ (Ret ()))) @ s {{ Φ }}.
  Proof.
    iIntros "#Hcoroutines Hstack Hpt H".
    iApply (wp_label_hom _ _ _ l _ _ _ g with "Hcoroutines Hstack").
    iNext.
    iIntros "Hstack".
    iApply (wp_generator with "Hcoroutines Hstack Hpt").
    iNext. iIntros "Hstack Hpt".
    iSimpl.
    iApply ("H" with "Hstack Hpt").
  Qed.

End lib.
