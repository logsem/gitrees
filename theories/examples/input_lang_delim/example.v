From gitrees Require Import gitree.
From gitrees.examples.input_lang_delim Require Import lang interp.
Require Import gitrees.lang_generic.
From iris.algebra Require Import gmap excl auth gmap_view.
From iris.proofmode Require Import base classes tactics environments.
From iris.base_logic Require Import algebra.

Open Scope syn_scope.

Example p : expr Empty_set :=
  ((#1) + (reset ((#3) + (shift/cc ((($0) @k #5) + (($0) @k #6)))))).

Local Definition rs : gReifiers _ _ := gReifiers_cons reify_delim gReifiers_nil.
(* Local Definition Hrs : subReifier reify_delim rs. *)
(* Proof. unfold rs. apply subReifier_here. Qed. *)

Notation F := (gReifiers_ops rs).
Context {R} `{!Cofe R}.
Context `{!SubOfe natO R, !SubOfe unitO R}.
Notation IT := (IT F R).
Notation ITV := (ITV F R).
Context (env : @interp_scope F R _ Empty_set).

Example ts := interp_config rs (Cexpr p) env.
Definition t := fst ts.
Definition σ := snd ts.


Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
Notation iProp := (iProp Σ).

Lemma wp_t (s : gitree.weakestpre.stuckness) :
  has_substate σ -∗
  WP@{rs} t @ s {{βv, βv ≡ RetV 18}}.
Proof.
  Opaque SHIFT APP_CONT.
  iIntros "Hσ".
  cbn.
  (* first, reset *)
  lazymatch goal with
  | |- context G [ofe_mor_car _ _ RESET ?t] => set (e := t)
  end.
  lazymatch goal with
  | |- context G [ofe_mor_car _ _ 𝒫 (?kk (ofe_mor_car _ _ RESET e))] => remember (𝒫 ◎ kk) as k
  end.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => set (α := t)
  end.
  assert (NonExpansive k).
  { subst. intros ????. solve_proper. }
  assert (α ≡ (λne x, k x) (RESET e)) as -> by (by simpl; subst).
  clear α.
  iApply (wp_reset with "Hσ").
  { subst. simpl. 
    simple refine (IT_HOM _ _ _ _ _ ); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro. simpl. done.
    - by rewrite !hom_err.
  }
  iIntros "!> Hl Hσ".
  simpl.

  (* then, shift *)
  lazymatch goal with
  | |- context G [ofe_mor_car _ _ SHIFT ?e] => set (f := e)
      (* envs_entails _ (wp _ (ofe_mor_car _ _ SHIFT ?e) _ _ _) => idtac *)
  end.
  lazymatch goal with
  | |- context G [?kk (ofe_mor_car _ _ SHIFT f)] => remember (𝒫 ◎ kk) as k'
  end.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => set (α := t)
  end.
  assert (NonExpansive k').
  { subst. intros ????. solve_proper. }
  assert (α ≡ (λne y, k' y) (SHIFT f)) as -> by (by simpl; subst).
  clear α.
  iApply (wp_shift with "Hσ").
  { subst. simpl. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. by intro.
    - by rewrite !hom_err.
  }
  iIntros "!>_ Hσ".
  simpl.

  (* the rest *)
  lazymatch goal with
  | |- context G [ofe_mor_car _ _ (get_val ?f) (_ 5)] => remember f as func
  end.
  lazymatch goal with
  | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ (NATOP _) ?x) ?y] =>
      remember x as ex; remember y as ey
  end.
  remember (λ (x y : IT), 𝒫 $ NATOP (do_natop lang.Add) x y) as kplus.
  assert (NonExpansive2 kplus).
  { subst. intros ???????. solve_proper. }
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => set (α := t)
  end.
  assert (α ≡ kplus (func (Ret 5)) (func (Ret 6))) as ->.
  { subst kplus α ex ey. f_equiv. f_equiv.
    - f_equiv. rewrite -IT_of_V_Ret. apply get_val_ITV'.
    - rewrite -IT_of_V_Ret. apply get_val_ITV'.
  }
  subst func. simpl.
  clear α.
  lazymatch goal with
  | |- context G [kplus ?scd (ofe_mor_car _ _ (get_fun ?f)
                           (ofe_mor_car _ _ Fun ?g))] => remember f as func1; remember g as gfunc; remember scd as snd
  end.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => set (α := t)
  end.
  assert (α ≡ kplus snd (func1 gfunc)) as ->.
  { subst α kplus func1 gfunc. repeat f_equiv; first by subst.
    simpl. by rewrite get_fun_fun.
  }
  subst func1 gfunc. simpl.
  remember (λ x, kplus snd x) as kkkk.
  assert (NonExpansive kkkk) by solve_proper.
  clear α.
  lazymatch goal with
  | |- context G [kkkk ?e] => remember e as newe
  end.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => set (α := t)
  end.

  assert (α ≡ (λne x, kkkk x) newe) as -> by (by subst).
  subst newe; clear α.
  iApply (wp_app_cont with "Hσ").
  { subst. simpl.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro. by simpl.
    - by rewrite !hom_err.
  }
  simpl.
  iIntros "!> _ Hσ".
  rewrite later_map_Next -Tick_eq.
  iApply wp_tick. iNext.
  subst. simpl.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => set (α := t)
  end.
  assert (α ≡ 𝒫 (IT_of_V $ RetV 9)) as ->.
  { subst α. f_equiv. by rewrite NATOP_Ret. }
  iApply (wp_pop_cons with "Hσ").
  iIntros "!> _ Hσ".
  simpl.
  lazymatch goal with
  | |- context G [ofe_mor_car _ _ (get_fun ?f)
                    (ofe_mor_car _ _ Fun ?g)] => remember f as func1; remember g as gfunc
  end.
  clear α.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) =>
      assert (t ≡ 𝒫 $ NATOP (do_natop lang.Add) (func1 gfunc) (IT_of_V (RetV 9)))
      as -> by (repeat f_equiv; apply get_fun_fun)
  end.
  subst. simpl.
  remember (λ x : IT, 𝒫 (NATOP (do_natop lang.Add) x (IT_of_V (RetV 9)))) as kkkk.
  assert (NonExpansive kkkk) by solve_proper.

  lazymatch goal with
  | |- context G [ofe_mor_car _ _ (ofe_mor_car _ _ (NATOP _) ?e) (IT_of_V (ofe_mor_car _ _ RetV 9))] => remember e as newe
  end.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) =>
      assert (t ≡ (λne x, kkkk x) newe)
      as -> by by subst
  end.
  subst newe.
  iApply (wp_app_cont with "Hσ").
  { subst. simpl. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite NATOP_ITV_Tick_l hom_tick.
    - rewrite NATOP_ITV_Vis_l hom_vis. f_equiv. by intro.
    - by rewrite NATOP_Err_l hom_err.
  }
  iIntros "!> _ Hσ". simpl.
  rewrite later_map_Next -Tick_eq. iApply wp_tick. iNext.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => assert (t ≡ 𝒫 (IT_of_V $ RetV 8))
      as -> by (f_equiv; by rewrite NATOP_Ret)
  end.
  iApply (wp_pop_cons with "Hσ").
  iIntros "!> _ Hσ".
  simpl. subst kkkk.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => assert (t ≡ 𝒫 (IT_of_V $ RetV 17))
      as -> by (f_equiv; by rewrite NATOP_Ret)
  end.
  iApply (wp_pop_cons with "Hσ").
  iIntros "!> _ Hσ".
  simpl.
  lazymatch goal with
  | |- envs_entails _ (wp _ ?t _ _ _) => assert (t ≡ 𝒫 (IT_of_V $ RetV 18))
      as -> by (f_equiv; by rewrite NATOP_Ret)
  end.
  iApply (wp_pop_end with "Hσ").
  iIntros "!> _ _".
  iApply wp_val. done.
Qed.
