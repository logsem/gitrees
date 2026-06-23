From gitrees Require Import gitree program_logic.
From gitrees.effects Require Import store fork.
From iris.algebra.lib Require Import excl_auth.
Import faa_wp.

Section counter.
  Context {n' : nat} (rs : gReifiers NotCtxDep n').
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_fork rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R, !SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Program Definition new_counter : (locO -n> IT) -n> IT := ALLOC (Ret 0).

  Definition read_counter : locO -n> IT := READ.

  Program Definition incr_fun : natO -n> natO -n> natO := λne a b, a + b.
  Solve All Obligations with solve_proper.

  Program Definition incr : locO -n> IT := λne ℓ, FAA incr_fun ℓ (Ret 1).
  Solve All Obligations with solve_proper_please.

  Lemma incr_fun_S (m : nat) : incr_fun 1 m = S m.
  Proof. reflexivity. Qed.

  Section weakestpre.
    Context `{!gitreeGS_gen rs R Σ}.
    Context `{!heapG rs R Σ}.
    Notation iProp := (iProp Σ).

    Lemma wp_new_counter (k : locO -n> IT) s Φ `{!NonExpansive Φ} :
      heap_ctx rs -∗
      ▷▷ (∀ ℓ, pointsto ℓ (Ret 0) -∗ WP@{rs} k ℓ @ s {{ Φ }}) -∗
      WP@{rs} new_counter k @ s {{ Φ }}.
    Proof.
      iIntros "#Hctx H".
      iApply (wp_alloc with "Hctx H").
    Qed.

    Lemma wp_read_counter (ℓ : loc) (m : nat) s Φ :
      heap_ctx rs -∗
      ▷ pointsto ℓ (Ret m) -∗
      ▷▷ (pointsto ℓ (Ret m) -∗ Φ (RetV m)) -∗
      WP@{rs} read_counter ℓ @ s {{ Φ }}.
    Proof.
      iIntros "#Hctx Hp H".
      iApply (wp_read with "Hctx Hp").
      iNext. iNext. iIntros "Hp".
      iApply wp_val. by iApply "H".
    Qed.

    Lemma wp_incr (ℓ : loc) (m : nat) s Φ :
      heap_ctx rs -∗
      ▷ pointsto ℓ (Ret m) -∗
      ▷▷ (pointsto ℓ (Ret (S m)) -∗ Φ (RetV m)) -∗
      WP@{rs} incr ℓ @ s {{ Φ }}.
    Proof.
      iIntros "#Hctx Hp H".
      iApply (wp_faa_hom rs incr_fun ℓ m 1 s Φ idfun with "Hctx Hp [H]").
      do 2 iNext. iIntros "Hp".
      iApply wp_val. iModIntro.
      assert (incr_fun 1 m = S m) as -> by reflexivity.
      by iApply "H".
    Qed.

    Program Definition count_to_two : IT :=
      new_counter $ λne ℓ,
        SEQ (incr ℓ) (SEQ (incr ℓ) (read_counter ℓ)).
    Solve All Obligations with solve_proper_please.

    Lemma wp_count_to_two s :
      heap_ctx rs ⊢ WP@{rs} count_to_two @ s {{ βv, βv ≡ RetV 2 }}.
    Proof.
      iIntros "#Hctx".
      rewrite /count_to_two.
      iApply (wp_new_counter with "Hctx"). { solve_proper. }
      iNext. iNext. iIntros (ℓ) "Hp". simpl.
      iApply wp_seq. { solve_proper. }
      iApply (wp_incr with "Hctx Hp").
      iNext. iNext. iIntros "Hp". simpl.
      iApply wp_seq. { solve_proper. }
      iApply (wp_incr with "Hctx Hp").
      iNext. iNext. iIntros "Hp". simpl.
      iApply (wp_read_counter with "Hctx Hp").
      iNext. iNext. iIntros "Hp".
      done.
    Qed.

  End weakestpre.

  Section concurrent.
    Context `{!gitreeGS_gen rs R Σ}.
    Context `{!heapG rs R Σ}.
    Context `{!inG Σ (excl_authR boolO)}.
    Notation iProp := (iProp Σ).

    Definition counterN : namespace := nroot .@ "counter".

    Lemma bit_agree γ (a b : bool) :
      own γ (●E a) -∗ own γ (◯E b) -∗ ⌜a = b⌝.
    Proof.
      iIntros "H● H◯".
      by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agree_L.
    Qed.

    Lemma bit_update γ (a b a' : bool) :
      own γ (●E a) -∗ own γ (◯E b) ==∗ own γ (●E a') ∗ own γ (◯E a').
    Proof.
      iIntros "H● H◯".
      iMod (own_update_2 with "H● H◯") as "[$ $]".
      { apply excl_auth_update. }
      done.
    Qed.

    Definition is_counter (γ0 γ1 : gname) (ℓ : loc) : iProp :=
      inv counterN (∃ b0 b1 : bool,
        pointsto ℓ (Ret (Nat.b2n b0 + Nat.b2n b1))
        ∗ own γ0 (●E b0) ∗ own γ1 (●E b1)).

    Global Instance is_counter_persistent γ0 γ1 ℓ :
      Persistent (is_counter γ0 γ1 ℓ).
    Proof. apply _. Qed.

    Lemma wp_incr0 (γ0 γ1 : gname) (ℓ : loc) s Ψ :
      heap_ctx rs -∗
      is_counter γ0 γ1 ℓ -∗
      own γ0 (◯E false) -∗
      ▷ (∀ m : nat, own γ0 (◯E true) -∗ Ψ (RetV m)) -∗
      WP@{rs} incr ℓ @ s {{ Ψ }}.
    Proof.
      iIntros "#Hctx #Hinv Hf H".
      rewrite /incr /=.
      iApply (wp_faa_atomic_hom rs incr_fun ℓ 1
                (⊤ ∖ ↑(nroot.@"storeE")) (⊤ ∖ ↑(nroot.@"storeE") ∖ ↑counterN)
                s Ψ idfun with "Hctx").
      { solve_ndisj. }
      iInv counterN as (b0 b1) "(Hp & Ha0 & Ha1)" "Hcl".
      iModIntro.
      iExists (Nat.b2n b0 + Nat.b2n b1). iFrame "Hp".
      iNext. iNext. iIntros "Hp".
      iAssert (⌜b0 = false⌝)%I as %->.
      { iApply (bit_agree with "Ha0 Hf"). }
      iMod (bit_update γ0 false false true with "Ha0 Hf") as "[Ha0 Hf]".
      assert (Nat.b2n true + Nat.b2n b1
              = incr_fun 1 (Nat.b2n false + Nat.b2n b1)) as Hval.
      { rewrite incr_fun_S. simpl. lia. }
      iMod ("Hcl" with "[Hp Ha0 Ha1]") as "_".
      { iNext. iExists true, b1. rewrite Hval. iFrame "Hp Ha0 Ha1". }
      iModIntro. simpl.
      iApply wp_val.
      by iApply ("H" $! _ with "Hf").
    Qed.

    Lemma wp_incr1 (γ0 γ1 : gname) (ℓ : loc) s Ψ :
      heap_ctx rs -∗
      is_counter γ0 γ1 ℓ -∗
      own γ1 (◯E false) -∗
      ▷ (∀ m : nat, own γ1 (◯E true) -∗ Ψ (RetV m)) -∗
      WP@{rs} incr ℓ @ s {{ Ψ }}.
    Proof.
      iIntros "#Hctx #Hinv Hf H".
      rewrite /incr /=.
      iApply (wp_faa_atomic_hom rs incr_fun ℓ 1
                (⊤ ∖ ↑(nroot.@"storeE")) (⊤ ∖ ↑(nroot.@"storeE") ∖ ↑counterN)
                s Ψ idfun with "Hctx").
      { solve_ndisj. }
      iInv counterN as (b0 b1) "(Hp & Ha0 & Ha1)" "Hcl".
      iModIntro.
      iExists (Nat.b2n b0 + Nat.b2n b1). iFrame "Hp".
      iNext. iNext. iIntros "Hp".
      iAssert (⌜b1 = false⌝)%I as %->.
      { iApply (bit_agree with "Ha1 Hf"). }
      iMod (bit_update γ1 false false true with "Ha1 Hf") as "[Ha1 Hf]".
      assert (Nat.b2n b0 + Nat.b2n true
              = incr_fun 1 (Nat.b2n b0 + Nat.b2n false)) as Hval.
      { rewrite incr_fun_S. simpl. lia. }
      iMod ("Hcl" with "[Hp Ha0 Ha1]") as "_".
      { iNext. iExists b0, true. rewrite Hval. iFrame "Hp Ha0 Ha1". }
      iModIntro. simpl.
      iApply wp_val.
      by iApply ("H" $! _ with "Hf").
    Qed.

    Lemma wp_read_le (γ0 γ1 : gname) (ℓ : loc) s Ψ :
      heap_ctx rs -∗
      is_counter γ0 γ1 ℓ -∗
      own γ0 (◯E true) -∗
      ▷ (∀ k : nat, ⌜1 ≤ k ≤ 2⌝ -∗ Ψ (RetV k)) -∗
      WP@{rs} read_counter ℓ @ s {{ Ψ }}.
    Proof.
      iIntros "#Hctx #Hinv Hf H".
      rewrite /read_counter.
      iApply (wp_read_atomic_hom rs ℓ
                (⊤ ∖ ↑(nroot.@"storeE")) (⊤ ∖ ↑(nroot.@"storeE") ∖ ↑counterN)
                s Ψ idfun with "Hctx").
      { solve_ndisj. }
      iInv counterN as (b0 b1) "(Hp & Ha0 & Ha1)" "Hcl".
      iModIntro.
      iExists (Ret (Nat.b2n b0 + Nat.b2n b1)). iFrame "Hp".
      iNext. iNext. iIntros "Hp".
      iAssert (⌜b0 = true⌝)%I as %->.
      { iApply (bit_agree with "Ha0 Hf"). }
      iMod ("Hcl" with "[Hp Ha0 Ha1]") as "_".
      { iNext. iExists true, b1. iFrame "Hp Ha0 Ha1". }
      iModIntro. simpl.
      iApply wp_val.
      iApply ("H" $! (Nat.b2n true + Nat.b2n b1)).
      iPureIntro. destruct b1; simpl; lia.
    Qed.

    Program Definition par_incr : IT :=
      new_counter $ λne ℓ,
        SEQ (FORK (SEQ (incr ℓ) (Ret ())))
            (SEQ (incr ℓ) (read_counter ℓ)).
    Solve All Obligations with solve_proper_please.

    Definition counter_post : ITV → iProp :=
      λ βv, (∃ k : nat, ⌜1 ≤ k ≤ 2⌝ ∧ βv ≡ RetV k)%I.
    Global Instance counter_post_ne : NonExpansive counter_post.
    Proof. solve_proper. Qed.

    Lemma wp_par_incr s :
      (⊢ fork_post (RetV ())) →
      fork_ctx rs -∗
      heap_ctx rs -∗
      WP@{rs} par_incr @ s {{ counter_post }}.
    Proof using All.
      iIntros (Hfork) "#Hfctx #Hctx".
      rewrite /par_incr.
      iApply (wp_new_counter with "Hctx").
      iNext. iNext. iIntros (ℓ) "Hp". simpl.
      iApply fupd_wp.
      iMod (own_alloc (●E false ⋅ ◯E false)) as (γ0) "[Ha0 Hf0]".
      { apply excl_auth_valid. }
      iMod (own_alloc (●E false ⋅ ◯E false)) as (γ1) "[Ha1 Hf1]".
      { apply excl_auth_valid. }
      iMod (inv_alloc counterN _
              (∃ b0 b1 : bool, pointsto ℓ (Ret (Nat.b2n b0 + Nat.b2n b1))
                 ∗ own γ0 (●E b0) ∗ own γ1 (●E b1))
              with "[Hp Ha0 Ha1]") as "#Hinv".
      { iNext. iExists false, false. simpl. iFrame "Hp Ha0 Ha1". }
      iModIntro.
      iApply wp_seq.
      iApply (wp_fork with "Hfctx [Hf1] [Hf0]").
      - iNext. iApply wp_seq.
        iApply (wp_incr1 with "Hctx Hinv Hf1").
        iNext. iIntros (m) "_". iApply wp_val. iModIntro. by iApply Hfork.
      - iNext. iApply wp_seq.
        iApply (wp_incr0 with "Hctx Hinv Hf0").
        iNext. iIntros (m) "Hf0".
        iApply (wp_read_le with "Hctx Hinv Hf0").
        iNext. iIntros (k) "%Hk".
        rewrite /counter_post. iExists k. by iSplit.
    Qed.

  End concurrent.

End counter.
