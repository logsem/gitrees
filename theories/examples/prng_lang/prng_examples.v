(*
   Examples demonstrating programming and reasoning with the PRNG effect.
   Randomized algorithms and their partial correctness.
 *)
From gitrees Require Import gitree program_logic.
From gitrees.effects Require Import prng store.
From gitrees.lib Require Import while.

Section prng_examples.
  Context {sz : nat} (rs : gReifiers NotCtxDep sz).
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_prng rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R, !SubOfe unitO R, !SubOfe locO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!gitreeGS_gen rs R Σ}.
  Context `{!heapG rs R Σ} `{prngG Σ}.
  Notation iProp := (iProp Σ).

  Notation wp_new := (wp_new rs).
  Notation wp_seed := (wp_seed rs).
  Notation wp_gen := (wp_gen rs).
  Notation wp_alloc := (wp_alloc rs).
  Notation wp_read := (wp_read rs).
  Notation wp_write := (wp_write rs).
  Notation wp_bind := (wp_bind rs).

  Definition neg_bool : IT -> IT := NATOP Nat.sub (Ret 1).

  Definition las_vegas_ITF (sd : nat) (init : nat) (test : IT) : IT :=
    PRNG_NEW $ λne r,
    ALLOC (Ret init) $ λne s,
    SEQ (PRNG_SEED r sd) $
    SEQ (WHILE
            (neg_bool (test ⊙ (READ s)))
            (LET (PRNG_GEN r) (WRITE s))) $
    READ s.

  Lemma wp_las_vegas_ITF (f : nat -> bool) (fIT : IT) (sd : nat) (init : nat) :
    heap_ctx rs
    -∗ prng_ctx rs
    -∗ □ (∀ n, WP@{rs} fIT ⊙ (Ret n) {{ β, β ≡ RetV (if f n then 1 else 0) }})
    -∗ WP@{rs} las_vegas_ITF sd init fIT {{ β, ∃ n, β ≡ RetV n ∧  f n ≡ true }}.
  Proof with (try solve_proper).
    (* preamble *)
    rewrite /las_vegas_ITF.
    iIntros "#Hheap #Hprng #Hf".
    iApply (wp_new with "Hprng")...
    iIntros "!>!> %r #Hr /=".
    iApply (wp_alloc with "Hheap")...
    iIntros "!>!> %s Hl /=".
    iApply wp_seq...
    iApply (wp_seed with "Hprng Hr").
    iIntros "!>!> _ /=".
    (* repeated retry *)
    iApply (wp_bind (SEQCtx _) _)...
    iLöb as "IH" forall (init).
    rewrite {2}(WHILE_eq _ _).
    iApply (wp_bind (IFSCtx _ _) _)...
    iApply (wp_bind neg_bool _)...
    iApply (wp_bind (AppRSCtx fIT) _)...
    iApply (wp_read with "Hheap Hl").
    iIntros "!>!> Hl /=".
    iApply wp_val; iModIntro.
    iPoseProof ("Hf" $! init) as "Hf0".
    rewrite /AppRSCtx IT_of_V_Ret.
    iApply (wp_wand with "Hf0").
    iIntros "%v Hv !>".
    iRewrite "Hv".
    rewrite /IFSCtx IT_of_V_Ret.
    destruct (f init) eqn:Hdec;
    rewrite /neg_bool NATOP_Ret /=;
    iApply wp_val; iModIntro;
    rewrite IT_of_V_Ret.
    - rewrite IF_False; last lia.
      iApply wp_val; iModIntro.
      rewrite /SEQCtx IT_of_V_Ret SEQ_Val.
      iApply (wp_read with "Hheap Hl").
      iIntros "!>!> _".
      iApply wp_val; iModIntro.
      by iExists init.
    - rewrite IF_True; last lia.
      iApply (wp_bind (SEQCtx _) _)...
      iApply wp_let...
      iApply (wp_gen with "Hprng Hr").
      iIntros "!>!> _ %n".
      iApply (wp_write with "Hheap Hl").
      iIntros "!>!> Hl".
      rewrite /SEQCtx !IT_of_V_Ret SEQ_Val.
      iApply wp_tick.
      iIntros "!> _".
      iApply ("IH" $! n with "Hl").
  Qed.
End prng_examples.
