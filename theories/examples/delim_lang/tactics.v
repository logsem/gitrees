From gitrees Require Import gitree lang_generic.
From iris.proofmode Require Import base classes tactics environments.
From iris.base_logic Require Import algebra.

(* TODO: doc *)
Ltac reshape_term α tac :=
  match α with
  | (ofe_mor_car _ _ (λne x, ?k1 x) (ofe_mor_car _ _ (?k2 ?t) ?e)) =>
      assert (AsVal e) by apply _;
      tac ((λne x, k1 (k2 x e)) t)
  | (ofe_mor_car _ _ (λne x, ?k1 x) (?k2 ?t)) =>
      tac ((λne x, k1 (k2 x)) t)
  | (ofe_mor_car _ _ (?k ?t) ?e) =>
      assert (AsVal e) by apply _;
      tac ((λne x, k x e) t)
  | (?k ?t) =>
      tac ((λne x, k x) t)
  end.

(* TODO: doc *)
Ltac wp_ctx :=
  match goal with
    |- envs_entails _ (wp _ ?e _ _ _) =>
      reshape_term e ltac:(fun x => assert (e ≡ x) as -> by done)
  end.

(* TODO: doc *)
Ltac name_ctx k :=
  match goal with
    |- envs_entails _ (wp _ (ofe_mor_car _ _ ?k1 _) _ _ _) =>
      remember k1 as k
  end.
