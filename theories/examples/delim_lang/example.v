From gitrees Require Import gitree lang_generic.
From gitrees.examples.delim_lang Require Import lang interp tactics.
From iris.proofmode Require Import base classes tactics environments.
From iris.base_logic Require Import algebra.

Open Scope syn_scope.

Example p : expr Empty_set :=
  ((#7) + (reset ((#7) * (shift/cc ((($0) @k #2) + (($0) @k #3)))))).

Local Definition rs : gReifiers _ _ := gReifiers_cons reify_delim gReifiers_nil.

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
  WP@{rs} t @ s {{βv, βv ≡ RetV 42}}.
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
  rewrite (get_val_ret _ 3). simpl.
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
  rewrite (get_val_ret _ 2). simpl.
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
