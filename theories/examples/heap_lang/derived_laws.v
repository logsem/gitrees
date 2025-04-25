(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

We collect both the total WP [twp_X] and partial WP [wp_X] versions of the laws.
The versions with later credits [wp_X_lc] are omitted because they are too
specific and can simply be derived using [twp_wp_step_lc] when needed.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array]. *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Export primitive_laws.
From iris.heap_lang Require Import tactics notation.
From iris.prelude Require Import options.

(** The [array] connective is a version of [pointsto] that works
with lists of values. *)

Definition array `{!heapGS_gen hlc Σ} (l : loc) (dq : dfrac) (vs : list val) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v.

Notation "l ↦∗ dq vs" := (array l dq vs)
  (at level 20, dq custom dfrac  at level 1, format "l  ↦∗ dq  vs") : bi_scope.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context `{!heapGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦∗{#q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦∗{#q} vs) (λ q, l ↦∗{#q} vs)%I q.
Proof. split; done || apply _. Qed.

Lemma array_nil l dq : l ↦∗{dq} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l dq v : l ↦∗{dq} [v] ⊣⊢ l ↦{dq} v.
Proof. by rewrite /array /= right_id Loc.add_0. Qed.

Lemma array_app l dq vs ws :
  l ↦∗{dq} (vs ++ ws) ⊣⊢ l ↦∗{dq} vs ∗ (l +ₗ length vs) ↦∗{dq} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite Loc.add_assoc.
Qed.

Lemma array_cons l dq v vs : l ↦∗{dq} (v :: vs) ⊣⊢ l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs.
Proof.
  rewrite /array big_sepL_cons Loc.add_0.
  setoid_rewrite Loc.add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l dq v vs R Q :
  Frame false R (l ↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q →
  Frame false R (l ↦∗{dq} (v :: vs)) Q | 2.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l dq vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{dq} vs -∗ ((l +ₗ off) ↦{dq} v ∗ ∀ v', (l +ₗ off) ↦{dq} v' -∗ l ↦∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs) as H by (apply lookup_lt_is_Some; by eexists).
  rewrite length_take min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite length_take min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

(** * Rules for allocation *)
Lemma pointsto_seq_array l dq v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦{dq} v) -∗
  l ↦∗{dq} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n' IH] forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc. iApply "IH". done.
Qed.

Lemma wp_allocN s E v n :
  (0 < n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_allocN_vec s E v n :
  (0 < n)%Z →
  {{{ True }}}
    AllocN #n v @ s ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN_vec; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

(** * Rules for accessing array elements *)
Lemma wp_load_offset s E l dq off vs v :
  vs !! off = Some v →
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; l ↦∗{dq} vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗{dq} vs }}}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma wp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_xchg_offset s E l off vs v v' :
  vs !! off = Some v →
  {{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v' @ s; E {{{ RET v; l ↦∗ <[off:=v']> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_xchg_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
   {{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v @ s; E {{{ RET (vs !!! off); l ↦∗ vinsert off v vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_fail_offset s E l dq off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v0, #false); l ↦∗{dq} vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_fail_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗{dq} vs }}}.
Proof.
  intros. eapply wp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma wp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset with "H"); [by eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

End lifting.

Global Typeclasses Opaque array.
