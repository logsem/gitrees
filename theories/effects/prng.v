(** pseudo random number generator effect *)
From iris.algebra Require Import gmap excl auth gmap_view list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.
From gitrees Require Import prelude.
From gitrees Require Import gitree.
From gitrees.lib Require Import eq.

Section prng_effect.

Opaque laterO_map.

Canonical Structure locO := leibnizO loc.

(*
   TODO: keep track of the state update and read out functions represented as GIT
   [stateF : oFunctor := (gmapOF locO ((▶ ∙) * (▶ ∙)))%OF;]
   [Ins := ((▶ ∙) * (▶ ∙))%OF;]
 *)
(* finite map of PRNG states: [Some seed] or [None] for deleted or unallocated. *)
Definition state := gmap loc nat.
Definition stateO : ofe := state.
Definition stateF : oFunctor := constOF state.

Definition read_lcg : natO -n> natO := λne n, n.
Definition update_lcg : natO -n> natO := λne n, (13 * n + 7) mod 23.
#[global] Opaque read_lcg update_lcg.

Definition state_new (σ : state) := let l := Loc.fresh (dom σ) in Some (l, <[l := 0]> σ).
Definition state_del (σ : state) (l : loc) := _ ← σ !! l; Some ((), delete l σ).
Definition state_gen (σ : state) (l : loc) := n ← σ !! l; Some (read_lcg n, <[l := update_lcg n]> σ).
Definition state_seed (σ : state) (l : loc) (sd : nat) := _ ← σ !! l; Some ((), <[l := sd]> σ).

Definition lift_post {A B} : option (A * state) -> option (A * state * list B)
  := option_map (fun '(a,st) => (a,st,[])).

Instance state_inhabited `{Cofe X} : Inhabited (stateF ♯ X).
Proof.
  constructor.
  constructor.
  constructor.
Qed.
Instance state_cofe `{Cofe X} : Cofe (stateF ♯ X).
Proof.
  apply gmap_cofe.
Qed.

Program Definition NewPrngE : opInterp :=  {|
  Ins := unitO;
  Outs := locO;
|}.
Definition reify_new X `{Cofe X}
  : (Ins NewPrngE ♯ X) * (stateF ♯ X)
  → option (Outs NewPrngE ♯ X * (stateF ♯ X) * listO (laterO X))
  := λ '((),s), lift_post $ state_new s.
#[export] Instance reify_new_ne X `{!Cofe X} :
  NonExpansive (reify_new X : prodO (Ins NewPrngE ♯ X) (stateF ♯ X)
                            → optionO (Outs NewPrngE ♯ X * (stateF ♯ X) * listO (laterO X))%type).
Proof. solve_proper. Qed.


Program Definition DelPrngE : opInterp :=  {|
  Ins := locO;
  Outs := unitO;
|}.
Definition reify_del X `{Cofe X}
  : (Ins DelPrngE ♯ X) * (stateF ♯ X)
  → option (Outs DelPrngE ♯ X * (stateF ♯ X) * listO (laterO X))
  := λ '(l,s), lift_post $ state_del s l.
#[export] Instance reify_del_ne X `{!Cofe X} :
  NonExpansive (reify_del X : prodO (Ins DelPrngE ♯ X) (stateF ♯ X)
                            → optionO (Outs DelPrngE ♯ X * (stateF ♯ X) * listO (laterO X))%type).
Proof. solve_proper. Qed.


Program Definition GenPrngE : opInterp :=  {|
  Ins := locO;
  Outs := natO;
|}.
Definition reify_gen X `{Cofe X}
  : (Ins GenPrngE ♯ X) * (stateF ♯ X)
  → option (Outs GenPrngE ♯ X * (stateF ♯ X) * listO (laterO X))
  := λ '(l,s), lift_post $ state_gen s l.
#[export] Instance reify_gen_ne X `{!Cofe X} :
  NonExpansive (reify_gen X : prodO (Ins GenPrngE ♯ X) (stateF ♯ X)
                            → optionO (Outs GenPrngE ♯ X * (stateF ♯ X) * listO (laterO X))%type).
Proof. solve_proper. Qed.

Program Definition SeedPrngE : opInterp :=  {|
  Ins := locO * natO;
  Outs := unitO;
|}.
Definition reify_seed X `{Cofe X}
  : (Ins SeedPrngE ♯ X) * (stateF ♯ X)
  → option (Outs SeedPrngE ♯ X * (stateF ♯ X) * listO (laterO X))
  := λ '((l,n),s), lift_post $ state_seed s l n.
#[export] Instance reify_seed_ne X `{!Cofe X} :
  NonExpansive (reify_seed X : prodO (Ins SeedPrngE ♯ X) (stateF ♯ X)
                             → optionO (Outs SeedPrngE ♯ X * (stateF ♯ X) * listO (laterO X))%type).
Proof. solve_proper. Qed.


Definition prngE : opsInterp := @[NewPrngE;DelPrngE;GenPrngE;SeedPrngE].
Program Canonical Structure reify_prng : sReifier NotCtxDep :=
  Build_sReifier NotCtxDep prngE stateF _ _ _.
Next Obligation.
  intros X HX op.
  destruct op as [| [| [| [| []]]]]; simpl.
  - simple refine (OfeMor (reify_new X)).
  - simple refine (OfeMor (reify_del X)).
  - simple refine (OfeMor (reify_gen X)).
  - simple refine (OfeMor (reify_seed X)).
Defined.

End prng_effect.

Section prng_combinators.
  Context {E : opsInterp}.
  Context `{!subEff prngE E}.
  Context {R} `{!Cofe R}.
  Context `{Base_nat : !SubOfe natO R} `{Base_unit : !SubOfe unitO R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Notation opid_new := (inl ()).
  Notation opid_del := (inr opid_new).
  Notation opid_gen := (inr opid_del).
  Notation opid_seed := (inr opid_gen).

  (* XXX: we have to specify [op] otherwise a weird proof obligation will be generated. *)
  Program Definition PRNG_NEW : (locO -n> IT) -n> IT :=
    λne k, Vis (E:=E) (subEff_opid opid_new)
               (subEff_ins (F:=prngE) (op:=opid_new) ())
               (NextO ◎ k ◎ (subEff_outs (op:=opid_new) ^-1)).
  Solve Obligations with solve_proper.

  Program Definition PRNG_DEL_k : locO -n> (unitO -n> IT) -n> IT :=
    λne l k, Vis (E:=E) (subEff_opid opid_del)
                 (subEff_ins (F:=prngE) (op:=opid_del) l)
                 (NextO ◎ k ◎ (subEff_outs (op:=opid_del) ^-1)).
  Solve Obligations with solve_proper.
  Definition PRNG_DEL := λne l, PRNG_DEL_k l Ret.

  Program Definition PRNG_GEN_k : locO -n> (natO -n> IT) -n> IT :=
    λne l k, Vis (E:=E) (subEff_opid $ opid_gen)
                 (subEff_ins (F:=prngE) (op:=opid_gen) l)
                 (NextO ◎ k ◎ (subEff_outs (op:=opid_gen)^-1)).
  Solve Obligations with solve_proper.
  Definition PRNG_GEN := λne l, PRNG_GEN_k l Ret.

  Program Definition PRNG_SEED_k : locO -n> natO -n> (unitO -n> IT) -n> IT :=
    λne l n k, Vis (E:=E) (subEff_opid $ opid_seed)
                   (subEff_ins (F:=prngE) (op:=opid_seed) (l, n))
                   (NextO ◎ k ◎ (subEff_outs (op:=opid_seed) ^-1)).
  Solve Obligations with solve_proper.
  Definition PRNG_SEED := λne l n, PRNG_SEED_k l n Ret.

  Ltac solve_hom_easy symbol :=
    unfold symbol;
    rewrite hom_vis/=; repeat f_equiv;
    intro x; cbn-[laterO_map]; rewrite laterO_map_Next;
    done.

  Lemma hom_NEW k f `{!IT_hom f} : f (PRNG_NEW k) ≡ PRNG_NEW (OfeMor f ◎ k).
  Proof. solve_hom_easy PRNG_NEW. Qed.

  Lemma hom_DEL_k l k f `{!IT_hom f} : f (PRNG_DEL_k l k) ≡ PRNG_DEL_k l (OfeMor f ◎ k).
  Proof. solve_hom_easy PRNG_DEL_k. Qed.

  Lemma hom_GEN_k l k f `{!IT_hom f} : f (PRNG_GEN_k l k) ≡ PRNG_GEN_k l (OfeMor f ◎ k).
  Proof. solve_hom_easy PRNG_GEN_k. Qed.

  Lemma hom_SEED_k l n k f `{!IT_hom f} : f (PRNG_SEED_k l n k) ≡ PRNG_SEED_k l n (OfeMor f ◎ k).
  Proof. solve_hom_easy PRNG_SEED_k. Qed.
End prng_combinators.

Section wp.
  Context {grs_sz : nat}.
  Context {a : is_ctx_dep}.
  Variable (rs : gReifiers a grs_sz).
  Context {R} {CR : Cofe R}.
  Context {SO : SubOfe unitO R} {SN : SubOfe natO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation stateO := (stateF ♯ IT).

  Definition istate := gmap_viewR loc natO.
  Class prngPreG Σ := PrngPreG { PrngPreG_inG :: inG Σ istate }.
  Class prngG Σ := PrngG {
      prngG_inG :: inG Σ istate;
      prngG_name : gname;
    }.
  Definition prngΣ : gFunctors := GFunctor istate.
  #[export] Instance subG_prngΣ {Σ} : subG prngΣ Σ → prngPreG Σ.
  Proof. solve_inG. Qed.

  Lemma new_prngG σ `{!prngPreG Σ} :
    (⊢ |==> ∃ `{!prngG Σ}, own prngG_name (●V σ): iProp Σ)%I.
  Proof.
    iMod (own_alloc (●V σ)) as (γ) "H".
    { apply gmap_view_auth_valid. }
    pose (sg := {| prngG_inG := _; prngG_name := γ |}).
    iModIntro. iExists sg. by iFrame.
  Qed.

  Context `{!subReifier (sReifier_NotCtxDep_min reify_prng a) rs}.
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Context `{!prngG Σ}.

  Program Definition prng_ctx :=
    inv (nroot.@"prngE")
      (∃ σ, £ 1 ∗ has_substate σ ∗ own prngG_name (●V σ))%I.

  Program Definition has_prng_state (l : loc) (s : nat) : iProp :=
    own prngG_name $ gmap_view_frag l (DfracOwn 1) s.
  Global Instance has_state_proper l : Proper ((≡) ==> (≡)) (has_prng_state l).
  Proof. solve_proper. Qed.
  Global Instance has_state_ne l : NonExpansive (has_prng_state l).
  Proof. solve_proper. Qed.

  Lemma istate_alloc n l σ :
    σ !! l = None →
    own prngG_name (●V σ) ==∗ own prngG_name (●V (<[l:=n]>σ))
                   ∗ has_prng_state l n.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { by apply (gmap_view_alloc _ l (DfracOwn 1) n); eauto. }
    done.
  Qed.

  Lemma istate_read l n σ :
    own prngG_name (●V σ) -∗ has_prng_state l n
    -∗ (σ !! l) ≡ Some n.
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[%H [Hval HEQ]]".
    done.
  Qed.

  Lemma istate_loc_dom l n σ :
    own prngG_name (●V σ) -∗ has_prng_state l n -∗ ⌜is_Some (σ !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (istate_read with "Hinv Hloc") as "Hl".
    destruct (σ !! l) ; eauto.
    by rewrite option_equivI.
  Qed.

  Lemma istate_write l n n' σ :
    own prngG_name (●V σ) -∗ has_prng_state l n
    ==∗ own prngG_name (●V <[l:=n']>σ)
      ∗ has_prng_state l n'.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]"; last done.
    by apply gmap_view_replace.
  Qed.

  Lemma istate_delete l n σ :
    own prngG_name (●V σ) -∗ has_prng_state l n ==∗ own prngG_name (●V delete l σ).
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "$".
    { apply gmap_view_delete. }
    done.
  Qed.


  Lemma wp_new_hom (k : locO -n> IT) s Φ `{!NonExpansive Φ} (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷▷ (∀ l, has_prng_state l 0 -∗ WP@{rs} κ (k l) @ s {{ Φ }}) -∗
    WP@{rs} κ (PRNG_NEW k) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Ha".
    unfold PRNG_NEW; simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"prngE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    simpl.
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    set (l:=Loc.fresh (dom σ)).
    (* current state, reification results, new state, continuation, thread pool additions *)
    iExists σ,l,(<[l:=0]>σ),(κ $ k l),[].
    iFrame "Hs".
    iSplit; first done.
    iSplit; first by rewrite later_map_Next ofe_iso_21.
    iNext.
    iMod (istate_alloc 0 l with "Hh") as "[Hh Hp]".
    {
      apply (not_elem_of_dom_1 (M:=gmap loc)).
      rewrite -(Loc.add_0 l).
      apply Loc.fresh_fresh.
      lia.
    }
    iIntros "Hlc Hs".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "Hemp".
    { iExists _. iFrame. }
    iModIntro.
    iSplit.
    - by iApply "Ha".
    - by iFrame.
  Qed.

  Lemma wp_new (k : locO -n> IT) s Φ `{!NonExpansive Φ} :
    prng_ctx -∗
    ▷▷ (∀ l, has_prng_state l 0 -∗ WP@{rs} k l @ s {{ Φ }}) -∗
    WP@{rs} PRNG_NEW k @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    iApply (wp_new_hom _ _ _ idfun with "Hh H").
  Qed.

  Lemma wp_del_k_hom (l : loc) (cont : unitO -n> IT) n s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷ has_prng_state l n -∗
    ▷▷ WP@{rs} κ (cont ()) @ s {{ β, Φ β }} -∗
    WP@{rs} κ (PRNG_DEL_k l cont) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    unfold PRNG_DEL_k; simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"prngE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    simpl.
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iAssert (⌜is_Some (σ !! l)⌝)%I as "%Hdom".
    { iApply (istate_loc_dom with "Hh Hp"). }
    destruct Hdom as [x Hx].
    (* current state, reification results, new state, continuation, thread pool additions *)
    iExists σ,(),(delete l σ),(κ $ cont ()),[].
    iFrame "Hs".
    iSplit.
    {
      iPoseProof (istate_read l n σ with "Hh Hp") as "%Hread".
      unfold lift_post, state_del.
      by rewrite Hread.
    }
    iSplit; first by rewrite later_map_Next ofe_iso_21.
    iNext.
    iMod (istate_delete l n σ with "Hh Hp") as "Hh".
    iIntros "Hlc Hs".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "Hemp".
    { iExists _. iFrame. }
    iModIntro.
    iSplit.
    - by iApply "Ha".
    - by iFrame.
  Qed.

  Lemma wp_del (l : loc) n s Φ :
    prng_ctx -∗
    ▷ has_prng_state l n -∗
    ▷ ▷ Φ (RetV ()) -∗
    WP@{rs} PRNG_DEL l @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hl H".
    iApply (wp_del_k_hom _ _ _ _ _ idfun with "Hctx Hl [H]").
    do 2 iNext.
    iApply wp_val.
    iModIntro. done.
  Qed.

  Lemma wp_gen_k_hom (l : loc) (cont : natO -n> IT) n s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷ has_prng_state l n -∗
    ▷▷ (has_prng_state l (update_lcg n) -∗ WP@{rs} κ (cont $ read_lcg n) @ s {{ Φ }}) -∗
    WP@{rs} κ (PRNG_GEN_k l cont) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    unfold PRNG_GEN_k; simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"prngE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    simpl.
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    (* current state, reification results, new state, continuation, thread pool additions *)
    iExists σ,(read_lcg n),(<[l:=update_lcg n]>σ),(κ (cont $ read_lcg n)),[].
    iFrame "Hs".
    iSplit.
    {
      iPoseProof (istate_read l n σ with "Hh Hp") as "%Hread".
      unfold lift_post, state_gen.
      by rewrite Hread.
    }
    iSplit; first by rewrite ofe_iso_21 later_map_Next.
    iNext.
    iMod (istate_write l n (update_lcg n) σ with "Hh Hp") as "[Hh Hp]".
    iIntros "Hlc Hs".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "Hemp".
    { iExists _. iFrame. }
    iModIntro.
    iSplit.
    - by iApply "Ha".
    - by iFrame.
  Qed.

  Lemma wp_gen (l : loc) (n : nat) s Φ :
    prng_ctx -∗
    ▷ has_prng_state l n -∗
    ▷ ▷ (has_prng_state l (update_lcg n) -∗ WP@{rs} (Ret $ read_lcg n) @ s {{ Φ }}) -∗
    WP@{rs} PRNG_GEN l @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    iApply (wp_gen_k_hom l Ret _ _ _ idfun with "Hcxt Hp Ha").
  Qed.

  Lemma wp_seed_k_hom (l : loc) n (cont : unitO -n> IT) n' s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷ has_prng_state l n -∗
    ▷▷ (has_prng_state l n' -∗ WP@{rs} κ (cont ()) @ s {{ Φ }}) -∗
    WP@{rs} κ (PRNG_SEED_k l n' cont) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    unfold PRNG_SEED_k; simpl.
    rewrite hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"prngE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    simpl.
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    (* current state, reification results, new state, continuation, thread pool additions *)
    iExists σ,(),(<[l:=n']>σ),(κ (cont ())),[].
    iFrame "Hs".
    iSplit.
    {
      iPoseProof (istate_read l n σ with "Hh Hp") as "%Hread".
      unfold lift_post, state_seed.
      by rewrite Hread.
    }
    iSplit; first by rewrite ofe_iso_21 later_map_Next.
    iNext.
    iMod (istate_write l n n' σ with "Hh Hp") as "[Hh Hp]".
    iIntros "Hlc Hs".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "Hemp".
    { iExists _. iFrame. }
    iModIntro.
    iSplit.
    - by iApply "Ha".
    - by iFrame.
  Qed.

  Lemma wp_seed (l : loc) n n' s Φ :
    prng_ctx -∗
    ▷ has_prng_state l n -∗
    ▷▷ (has_prng_state l n' -∗ Φ (RetV ())) -∗
    WP@{rs} PRNG_SEED l n' @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply (wp_seed_k_hom l n Ret _ _ _ idfun with "Hctx Hp [Ha]").
    do 2 iNext.
    iIntros "H".
    iDestruct ("Ha" with "H") as "G".
    iApply wp_val.
    by iModIntro.
  Qed.

End wp.

Arguments prng_ctx {_ _} rs {_ _ _ _ _ _}.
Arguments has_prng_state {_ _} _ _.
#[global] Opaque PRNG_NEW PRNG_DEL_k PRNG_GEN_k PRNG_SEED_k.

