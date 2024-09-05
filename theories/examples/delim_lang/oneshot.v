From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import cmra agree excl csum.
From iris.base_logic Require Import base_logic lib.own.

Definition oneshotR := csumR (exclR unit) (agreeR unitO).
Class oneshotG Σ := { oneshot_inG :: inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Global Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Definition pending `{oneshotG Σ} γ := own γ (Cinl (Excl ())).
Definition shot `{oneshotG Σ} γ := own γ (Cinr (to_agree ())).
Lemma new_pending `{oneshotG Σ} : ⊢ |==> ∃ γ, pending γ.
Proof. by apply own_alloc. Qed.
Lemma shoot `{oneshotG Σ} γ : pending γ ==∗ shot γ.
Proof. by iApply own_update; apply cmra_update_exclusive. Qed.
Lemma shot_not_pending `{oneshotG Σ} γ : shot γ -∗ pending γ -∗ False.
Proof. iIntros "Hs Hp". iDestruct (own_valid_2 with "Hs Hp") as %?; done. Qed.
