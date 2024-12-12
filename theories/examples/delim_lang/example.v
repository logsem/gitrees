(** * Example of a program in delim_lang and its symbolic execution *)
From gitrees Require Import gitree lang_generic.
From gitrees.effects Require Import delim store.
From gitrees.lib Require Import pairs.
From gitrees.examples.delim_lang Require Import lang interp.
From iris.proofmode Require Import base classes tactics environments.
From iris.base_logic Require Import algebra.

Open Scope syn_scope.

(** The program captures the inner continuation, invokes it with 5 and
6, and adds the results to 1. The result is 1+(3+5)+(3+6)=18 *)
Example p : expr Empty_set :=
  ((#1) + (reset ((#3) + (shift/cc ((($0) @k #5) + (($0) @k #6)))))).

Global Ltac shift_hom :=
  match goal with
  | |- envs_entails _ (wp _ (ofe_mor_car _ _ (λne x, ?k1 x) (?k2 ?t)) _ _ _) =>
      assert ((ofe_mor_car _ _ (λne x, k1 x) (k2 t)) ≡ (λne x, k1 (k2 x)) t) as -> by done
  | |- envs_entails _ (wp _ (?k ?t) _ _ _) =>
      assert (k t ≡ (λne x, k x) t) as -> by done
  end.

Global Ltac shift_natop_l :=
  match goal with
  | |- envs_entails _ (wp _ (ofe_mor_car _ _ (λne x, ?k1 x)
                              (((NATOP (do_natop ?op)) ?t) (IT_of_V ?e))) _ _ _) =>
      assert ((ofe_mor_car _ _ (λne x, k1 x) (NATOP (do_natop op) t (IT_of_V e))) ≡
                (λne x, k1 (NATOP (do_natop op) x (IT_of_V e))) t) as -> by done
  end.

Section proof.

  Context {sz : nat}.
  Variable rs : gReifiers CtxDep sz.
  Context `{!subReifier reify_delim rs}.

  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_t σ (s : gitree.weakestpre.stuckness) :
    (⊢ has_substate σ
       -∗ WP@{rs} (interp_expr _ p ı_scope) @ s
            {{ βv, βv ≡ RetV 18
                   ∗ has_substate σ }})%I.
  Proof.
    Opaque SHIFT APP_CONT.
    iIntros "Hσ".
    cbn.
    (* first, reset *)
    do 2 shift_hom.
    iApply (wp_reset with "Hσ").
    iIntros "!> _ Hσ". simpl.

    (* then, shift *)
    do 2 shift_hom.
    iApply (wp_shift with "Hσ").
    { rewrite laterO_map_Next. done. }
    iIntros "!>_ Hσ".
    simpl.

    (* the rest *)
    rewrite -(IT_of_V_Ret 6) get_val_ITV'. simpl.
    rewrite get_fun_fun. simpl.
    do 2 shift_hom.
    iApply (wp_app_cont with "Hσ"); first done.
    iIntros "!> _ Hσ". simpl.
    rewrite later_map_Next -Tick_eq.
    iApply wp_tick. iNext.
    shift_hom.
    rewrite IT_of_V_Ret NATOP_Ret. simpl.
    rewrite -(IT_of_V_Ret 9).
    iApply (wp_pop_cons with "Hσ").
    iIntros "!> _ Hσ".
    simpl.

    shift_hom.
    shift_natop_l.
    rewrite -(IT_of_V_Ret 5) get_val_ITV'. simpl.
    shift_hom. shift_natop_l.
    rewrite get_fun_fun. simpl.
    shift_hom. shift_natop_l.
    iApply (wp_app_cont with "Hσ"); first done.
    iIntros "!> _ Hσ". simpl.
    rewrite later_map_Next -Tick_eq.
    iApply wp_tick. iNext.
    rewrite (IT_of_V_Ret 5) NATOP_Ret. simpl.
    rewrite -(IT_of_V_Ret 8).
    iApply (wp_pop_cons with "Hσ").
    iIntros "!> _ Hσ".
    simpl.
    shift_hom.
    shift_natop_l.
    rewrite (IT_of_V_Ret 8).
    simpl. rewrite IT_of_V_Ret NATOP_Ret.
    simpl. rewrite -(IT_of_V_Ret 17).
    iApply (wp_pop_cons with "Hσ").
    iIntros "!> _ Hσ". simpl.
    rewrite IT_of_V_Ret NATOP_Ret.
    simpl. rewrite -(IT_of_V_Ret 18).
    iApply wp_val.
    iModIntro.
    iFrame "Hσ".
    done.
  Qed.

End proof.
