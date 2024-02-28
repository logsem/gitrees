From gitrees Require Import gitree lang_generic.
From gitrees.examples.delim_lang Require Import lang interp.
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


Ltac wp_ctx :=
  match goal with
  | |- envs_entails _ (wp _ (ofe_mor_car _ _ (λne x, ?k1 x)
                               (ofe_mor_car _ _ (?k2 ?t) ?e)) _ _ _) =>
      assert (AsVal e) by apply _;
      assert ((ofe_mor_car _ _ (λne x, k1 x) (k2 t e)) ≡ (λne x, k1 (k2 x e)) t) as -> by done
  | |- envs_entails _ (wp _ (ofe_mor_car _ _ (λne x, ?k1 x) (?k2 ?t)) _ _ _) =>
      assert ((ofe_mor_car _ _ (λne x, k1 x) (k2 t)) ≡ (λne x, k1 (k2 x)) t) as -> by done
  | |- envs_entails _ (wp _ (ofe_mor_car _ _ (?k ?t) ?e) _ _ _) =>
      assert (AsVal e) by apply _;
      assert (k t e ≡ (λne x, k x e) t) as -> by done
  | |- envs_entails _ (wp _ (?k ?t) _ _ _) =>
      assert (k t ≡ (λne x, k x) t) as -> by done
  end.

Ltac name_ctx k :=
  match goal with
  | |- envs_entails _ (wp _ (ofe_mor_car _ _ ?k1 _) _ _ _) =>
      remember k1 as k
  end.


Lemma wp_t (s : gitree.weakestpre.stuckness) :
  has_substate σ -∗
  WP@{rs} t @ s {{βv, βv ≡ RetV 18}}.
Proof.
  Opaque SHIFT APP_CONT.
  iIntros "Hσ".
  cbn.
  (* first, reset *)
  do 2 wp_ctx.
  iApply (wp_reset with "Hσ").
  iIntros "!> _ Hσ". simpl.

  (* then, shift *)
  do 2 wp_ctx.
  iApply (wp_shift with "Hσ"); first by rewrite laterO_map_Next.
  iIntros "!>_ Hσ". simpl.

  (* the rest *)
  rewrite (get_val_ret _ 6). simpl.
  rewrite get_fun_fun. simpl.
  do 2 wp_ctx.
  iApply (wp_app_cont with "Hσ"); first done.
  iIntros "!> _ Hσ". simpl.

  rewrite later_map_Next -Tick_eq.
  iApply wp_tick. iNext.
  rewrite NATOP_Ret. simpl.
  iApply (wp_pop_cons with "Hσ").
  iIntros "!> _ Hσ". simpl.

  do 2 wp_ctx. name_ctx k.                    (* so that it does't simpl *)
  rewrite (get_val_ret _ 5). simpl.
  rewrite get_fun_fun. simpl. subst k.
  iApply (wp_app_cont with "Hσ"); first done.
  iIntros "!> _ Hσ". simpl.

  rewrite later_map_Next -Tick_eq.
  iApply wp_tick. iNext.
  rewrite NATOP_Ret. simpl.
  iApply (wp_pop_cons with "Hσ").
  iIntros "!> _ Hσ". simpl.

  rewrite NATOP_Ret. simpl.
  iApply (wp_pop_cons with "Hσ").
  iIntros "!> _ Hσ". simpl.
  rewrite NATOP_Ret. simpl.
  iApply (wp_pop_end with "Hσ").
  iIntros "!> _ _".
  iApply wp_val. done.
Qed.
