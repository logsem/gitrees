From gitrees Require Import gitree gitree.subofe.

Ltac simplify_ret :=
  match goal with
  | H : context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Err ?a)] |- _ =>
      rewrite get_ret_err in H
  | H : context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Ret ?a)] |- _ =>
      rewrite get_ret_ret in H
  | H : context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Tick ?a)] |- _ =>
      rewrite get_ret_tick in H
  | H : context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Fun ?a)] |- _ =>
      rewrite get_ret_fun in H
  | H : context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ (Vis ?op ?i ?k))] |- _ =>
      rewrite get_ret_vis in H
  | |- context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Err ?a)] =>
      rewrite get_ret_err
  | |- context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Ret ?a)] =>
      rewrite get_ret_ret
  | |- context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Tick ?a)] =>
      rewrite get_ret_tick
  | |- context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ Fun ?a)] =>
      rewrite get_ret_fun
  | |- context G [ofe_mor_car _ _ (get_ret ?f) (ofe_mor_car _ _ (Vis ?op ?i ?k))] =>
      rewrite get_ret_err
  end.
