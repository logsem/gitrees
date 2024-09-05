(** This file has been taken from iris and edited accordingly. *)
(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
From gitrees Require Export examples.delim_lang.program_logic.weakestpre.
From iris.prelude Require Import options.

Section lifting.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n) {A} `{!Cofe A}.
  Notation rG := (gReifiers_sReifier rs).
  Notation F := (sReifier_ops rG).
  Notation IT := (IT F A).
  Notation ITV := (ITV F A).
  Notation stateF := (gReifiers_state rs).
  Notation stateO := (stateF ♯ IT).
  Notation stateR := (gReifiers_ucmra rs IT).
  Let of_state := (of_state rs IT).
  Let of_idx := (of_idx rs IT).
  Notation reify := (reify rG).
  Notation istep := (istep rG).
  Notation isteps := (isteps rG).
  Notation sstep := (sstep rG).
  Notation ssteps := (ssteps rG).

  Implicit Type op : opid F.
  Implicit Type α β : IT.

  Context `{!invGS Σ} `{!stateG rs A Σ} `{!gstacksIG Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).

  (* Lemma wbwp_pure_step_fupd E E' out e1 e2 φ m Φ : *)
  (*   (* PureExec φ n e1 e2 → *) *)
  (*   φ → *)
  (*   (|={E}[E']▷=>^n £ m *)
  (*    -∗ WBWP@{rs} e2 @ out; E {{ Φ }}) ⊢ WBWP@{rs} e1 @ out; E {{ Φ }}. *)
  (* Proof. *)
  (*   rewrite /wbwp. *)
  (*   iIntros ((* Hexec *) Hφ) "Hwp". *)
  (*   iIntros (M) "HM". *)
  (*   iApply wp_pure_step_fupd; first done. *)
  (*   iApply (step_fupdN_wand with "Hwp"). *)
  (*   iIntros "Hwp H". *)
  (*   iSpecialize ("Hwp" with "H HM"); done. *)
  (* Qed. *)

  (* Lemma wbwp_pure_step_later `{!Inhabited (state Λ)} E out e1 e2 φ n Φ : *)
  (*   PureExec φ n e1 e2 → *)
  (*   φ → *)
  (*   ▷^n (£ n -∗ WBWP e2 @ out; E {{ Φ }}) ⊢ WBWP e1 @ out; E {{ Φ }}. *)
  (* Proof. *)
  (*   intros Hexec ?. rewrite -wbwp_pure_step_fupd //. clear Hexec. *)
  (*   enough (∀ P, ▷^n P -∗ |={E}▷=>^n P) as Hwp by iApply Hwp. iIntros (?). *)
  (*   induction n as [|n IH]; simpl; first by auto. *)
  (*   iIntros; rewrite -step_fupd_intro; last done. iNext; iApply IH; done. *)
  (* Qed. *)
End lifting.
