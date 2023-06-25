(* Show how an imperative factorial refines a functional one
- Read a number from a tape
- Compute factorial
- ????
- REFINEMENT!!!111

 *)
From Equations Require Import Equations.
From gitrees Require Import gitree program_logic.
From gitrees.input_lang Require Import lang interp.
From gitrees.examples Require Import store while.


(* #[local] Definition V1 : var [();()] := Vs Vz. *)
#[local] Notation V1 := (Vs Vz).
Definition fact_expr : expr [].
Proof.
  refine (Rec (If (Var V1) (Val $ Lit 1)
                 (NatOp lang.Add (Var V1)
                    (App (Var Vz) (NatOp lang.Sub (Var V1) (Val $ Lit 1)))))).
Defined.

Section fact.
  Definition rs : gReifiers 2 :=
    gReifiers_cons reify_io (gReifiers_cons reify_store gReifiers_nil).
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F).
  Notation ITV := (ITV F).

  Context `{!invGS Σ, !stateG rs Σ, !heapG rs Σ}.
  Notation iProp := (iProp Σ).

  Definition fact_fun : IT := interp_expr rs fact_expr ().

  Program Definition fact_imp_body (n : nat) (acc ℓ : loc) : IT :=
    WHILE (READ ℓ) $
         LET (READ ℓ) $ λne i,
         LET (NATOP Nat.mul i (READ acc)) $ λne r,
         LET (NATOP Nat.sub i (Nat 1)) $ λne i,
         SEQ (WRITE acc r)
             (WRITE ℓ i).
  Solve All Obligations with solve_proper_please.

  Program Definition fact_imp : IT := λit n,
    flip get_nat n $ λ n,
    ALLOC (Nat 1) $ λne acc,
    ALLOC (Nat n) $ λne ℓ,
      SEQ
        (fact_imp_body n acc ℓ)
        (READ acc).

  Lemma wp_fact_imp_bod n m acc ℓ :
    heap_ctx -∗
    pointsto acc (Nat m) -∗ pointsto ℓ (Nat n) -∗
    WP@{rs} fact_imp_body n acc ℓ {{ _, pointsto acc (Nat (m * fact n)) }}.
  Proof.
    iIntros "#Hctx Hacc Hl".
    iLöb as "IH" forall (n m).
    unfold fact_imp_body.
    rewrite {2}(WHILE_eq (READ _)).
    iApply (wp_bind rs (IFSCtx _ (Nat 0)) (READ ℓ)).
    iApply (wp_read with "Hctx Hl").
    iNext. iNext. iIntros "Hl".
    iApply wp_val. iModIntro.
    unfold IFSCtx. simpl.
    destruct n as [|n].
    - rewrite IF_False; last lia.
      iApply wp_val. simpl. rewrite Nat.mul_1_r//.
    - rewrite IF_True; last lia.
      iApply wp_seq.
      iApply wp_let.
      iApply (wp_read with "Hctx Hl").
      iNext. iNext. iIntros "Hl".
      iApply wp_val. simpl.
      iApply wp_let.
      iApply (wp_bind _ (NatOpRSCtx _ (Nat (S n)))).
      { solve_proper_please. }
      iModIntro.
      iApply (wp_read with "Hctx Hacc").
      iNext. iNext. iIntros "Hacc".
      iApply wp_val. iModIntro.
      simpl. unfold NatOpRSCtx.
      rewrite NATOP_Nat.
      iApply wp_val. iModIntro.
      iApply wp_let.
      rewrite NATOP_Nat.
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
    heap_ctx ⊢ WP@{rs} fact_imp ⊙ (Nat n) {{  βv, βv ≡ NatV (fact n)  }}.
  Proof.
    iIntros "#Hctx".
    iApply wp_lam. iNext.
    simpl. rewrite get_nat_nat.
    iApply (wp_alloc with "Hctx").
    { solve_proper. }
    fold rs. iNext. iNext.
    iIntros (acc) "Hacc". simpl.
    iApply (wp_alloc with "Hctx").
    { solve_proper. }
    fold rs. iNext. iNext.
    iIntros (ℓ) "Hl". simpl.
    iApply wp_seq.
    { solve_proper. }
    iApply (wp_wand _ _ _ _ (λ _, pointsto acc (Nat $ fact n)) with "[-]"); last first.
    { simpl. iIntros (_) "Hacc".
      iModIntro. iApply (wp_read with "Hctx Hacc").
      iNext. iNext. iIntros "Hacc".
      iApply wp_val. done. }
    iPoseProof (wp_fact_imp_bod with "Hctx Hacc Hl") as "H".
    by rewrite Nat.mul_1_l.
  Qed.

  Program Definition fact_combined : IT :=
    INPUT $ λne n, fact_imp ⊙ (Nat n).
  Lemma wp_fact_combined (n : nat) :
    heap_ctx ∗ has_substate (State [n] [])
    ⊢ WP@{rs} get_nat OUTPUT fact_combined  {{ _, has_substate (State [] [fact n]) }}.
  Proof.
    iIntros "[#Hctx Htape]".
    unfold fact_combined.
    iApply (wp_bind _ (get_nat _)).
    iApply (wp_input with "Htape").
    { reflexivity. }
    iNext. iIntros "_ Htape". simpl.
    iApply (wp_wand).
    { iApply (wp_fact_imp with "Hctx"). }
    simpl. iIntros (v) "Hv". iModIntro.
    iRewrite "Hv". simpl. rewrite get_nat_nat.
    iApply (wp_output with "Htape").
    { compute-[fact]. done. }
    iNext. iIntros "_ $".
  Qed.

End fact.

