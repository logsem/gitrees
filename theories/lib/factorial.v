From gitrees Require Import gitree program_logic.
From gitrees.examples.input_lang Require Import lang interp.
From gitrees.effects Require Import store.
From gitrees.lib Require Import while.

Section fact.
  Context (n' : nat) (rs : gReifiers NotCtxDep n').
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R, !SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context `{!invGS Σ, !stateG rs R Σ, !heapG rs R Σ}.
  Notation iProp := (iProp Σ).

  Program Definition fact_imp_body (acc ℓ : loc) : IT :=
    WHILE (READ ℓ) $
         LET (READ ℓ) $ λne i,
         LET (NATOP Nat.mul i (READ acc)) $ λne r,
         LET (NATOP Nat.sub i (Ret 1)) $ λne i,
         SEQ (WRITE acc r)
             (WRITE ℓ i).
  Solve All Obligations with solve_proper_please.

  Program Definition fact_imp : IT := λit n,
    flip get_ret n $ λne (n : nat),
    ALLOC (Ret 1) $ λne acc,
    ALLOC (Ret n) $ λne ℓ,
      SEQ
        (fact_imp_body acc ℓ)
        (READ acc).

  Lemma wp_fact_imp_bod n m acc ℓ :
    @heap_ctx n' NotCtxDep rs R _ _ Σ _ _ _ -∗
    pointsto acc (Ret m) -∗ pointsto ℓ (Ret n) -∗
    WP@{rs} fact_imp_body acc ℓ {{ _, pointsto acc (Ret (m * fact n)) }}.
  Proof.
    iIntros "#Hctx Hacc Hl".
    iLöb as "IH" forall (n m).
    unfold fact_imp_body.
    rewrite {2}(WHILE_eq (READ _)).
    iApply (wp_bind rs (IFSCtx _ (Ret ())) (READ ℓ)).
    iApply (wp_read with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    unfold IFSCtx. simpl.
    iAssert ((IT_of_V (E:=F) (RetV n)) ≡ (Ret n))%I as "#Hn".
    { iPureIntro. apply (IT_of_V_Ret (B:=R)). }
    iRewrite "Hn".
    destruct n as [|n].
    - rewrite IF_False ; last lia.
      iApply wp_val. simpl. rewrite Nat.mul_1_r//.
    - rewrite IF_True; last lia.
      iApply wp_seq.
      iApply wp_let.
      iApply (wp_read with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val. simpl.
      iApply wp_let.
      iApply (wp_bind _ (NatOpRSCtx _ (Ret (S n)))).
      { solve_proper_please. }
      iModIntro.
      iApply (wp_read with "Hctx Hacc").
      iNext. iNext. iIntros "Hacc".
      iApply wp_val. iModIntro.
      simpl. unfold NatOpRSCtx.
      (* TODO: look at this with amin *)
      iAssert (IT_of_V (E:=F) (RetV m) ≡ (Ret m))%I as "#Hm".
      { iPureIntro. apply (IT_of_V_Ret (B:=R)). }
      iRewrite "Hm".
      rewrite NATOP_Ret.
      iApply wp_val. iModIntro.
      iApply wp_let.
      iAssert (IT_of_V (E:=F) (RetV (S n)) ≡ (Ret (S n)))%I as "#Hsn".
      { iPureIntro. apply (IT_of_V_Ret (B:=R)). }
      iRewrite "Hsn".
      rewrite NATOP_Ret.
      iApply wp_val. iModIntro.
      simpl.
      iApply wp_seq.
      iApply (wp_write with "Hctx Hacc").
      iNext. iNext. iIntros "Hacc".
      iApply (wp_write with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_tick. iNext.
      replace (m + n*m) with ((n + 1) * m) by lia.
      iSpecialize ("IH" with "Hacc  Hl" ).
      iApply (wp_wand with "IH").
      iIntros (_).
      rewrite Nat.sub_0_r.
      replace ((n + 1) * m * fact n) with (m * (fact n + n * fact n)) by lia.
      iIntros "$". done.
  Qed.

  Lemma wp_fact_imp (n : nat) :
    @heap_ctx n' NotCtxDep rs R _ _ Σ _ _ _ ⊢ WP@{rs} fact_imp ⊙ (Ret n) {{  βv, βv ≡ RetV (fact n)  }}.
  Proof.
    iIntros "#Hctx".
    iApply wp_lam. iNext.
    simpl. rewrite get_ret_ret.
    iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext.
    iIntros (acc) "Hacc". simpl.
    iApply (wp_alloc with "Hctx").
    { solve_proper. }
    iNext. iNext.
    iIntros (ℓ) "Hl". simpl.
    iApply wp_seq.
    { solve_proper. }
    iApply (wp_wand _ (λ _, pointsto acc (Ret $ fact n)) with "[-]"); last first.
    { simpl. iIntros (_) "Hacc".
      iModIntro. iApply (wp_read with "Hctx Hacc").
      iNext. iNext. iIntros "Hacc".
      iApply wp_val. done. }
    iPoseProof (wp_fact_imp_bod with "Hctx Hacc Hl") as "H".
    by rewrite Nat.mul_1_l.
  Qed.

  Program Definition fact_io : IT :=
    INPUT $ λne n, fact_imp ⊙ (Ret n).
  Lemma wp_fact_io (n : nat) :
    @heap_ctx n' NotCtxDep rs R _ _ Σ _ _ _ ∗ has_substate (State [n] [])
    ⊢ WP@{rs} get_ret OUTPUT fact_io  {{ _, has_substate (State [] [fact n]) }}.
  Proof.
    iIntros "[#Hctx Htape]".
    unfold fact_io.
    iApply (wp_bind _ (get_ret _)).
    iApply (wp_input with "Htape").
    { reflexivity. }
    iNext. iIntros "_ Htape". simpl.
    iApply (wp_wand).
    { iApply (wp_fact_imp with "Hctx"). }
    simpl. iIntros (v) "Hv". iModIntro.
    iRewrite "Hv". simpl. rewrite get_ret_ret.
    iApply (wp_output with "Htape").
    { compute-[fact]. done. }
    iNext. iIntros "_ $".
  Qed.

End fact.
