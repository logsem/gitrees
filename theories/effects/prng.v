(** pseudo random number generator effect *)
From iris.algebra Require Import gmap gset gmap_view excl agree auth.
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

(* NOTE: we cannot give a spec to delete *)
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

  (*
     an insert-only store with anonymous pointsto predicate

     pointsto l -∗ pointsto l ∗ pointsto l
     store σ ∗ pointsto l -∗ ∃ n, σ !! l ≡ Some n
     store σ ∗ pointsto l ==∗ <[l:=v]> σ ∗ pointsto l
  *)

  Definition entryUR := prodUR (optionUR (agreeR unit)) (optionUR (exclR natO)).
  Definition prngUR := authUR (gmapUR loc entryUR).

  Definition owner_entry n : entryUR := (Some (to_agree ()), Excl' n).
  Definition borrow_entry  : entryUR := (Some (to_agree ()), None).
  Definition owner_store σ  : prngUR := ● (owner_entry <$> σ).
  Definition borrow_store l : prngUR := ◯ {[l := borrow_entry]}.

  Class prngPreG Σ := PrngPreG { PrngPreG_inG :: inG Σ prngUR }.
  Class prngG Σ := PrngG {
      prngG_inG :: inG Σ prngUR;
      prngG_name : gname;
    }.
  Definition prngΣ : gFunctors := GFunctor prngUR.
  #[export] Instance subG_prngΣ {Σ} : subG prngΣ Σ → prngPreG Σ.
  Proof. solve_inG. Qed.

  Lemma new_storeG `{!prngPreG Σ} :
    (⊢ |==> ∃ `{!prngG Σ}, own prngG_name (owner_store ∅): iProp Σ)%I.
  Proof.
    iMod (own_alloc (owner_store ∅)) as (γ) "H1".
    {
      rewrite /owner_store auth_auth_valid //.
    }
    set {| prngG_inG := PrngPreG_inG; prngG_name := γ |} as sg.
    by iExists sg.
  Qed.

  Context `{!subReifier (sReifier_NotCtxDep_min reify_prng a) rs}.
  Context `{!gitreeGS_gen rs R Σ}.
  Notation iProp := (iProp Σ).

  Context `{!prngG Σ}.

  Notation own := (own prngG_name).
  Definition has_prngs (σ : gmapR loc nat) :=
    own $ owner_store σ.
  Definition known_prng (l : loc) :=
    own $ borrow_store l.
  Definition prng_ctx := inv (nroot.@"prngE") (∃ σ, £ 1 ∗ has_substate σ ∗ has_prngs σ)%I.

  Lemma istate_alloc (n : nat) l σ :
    σ !! l = None →
    has_prngs σ ==∗ has_prngs (<[l:=n]> σ) ∗ known_prng l.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[Hauth Hfrag]".
    {
      apply (auth_update_alloc (owner_entry <$> σ) (owner_entry <$> <[l:=n]> σ) {[l := owner_entry n]}).
      rewrite fmap_insert.
      apply alloc_local_update; last done.
      rewrite lookup_fmap Hl //.
    }
    unfold has_prngs, owner_store, borrow_store, known_prng.
    iMod (own_update with "Hauth") as "[$ $]"; last done.
    {
      apply auth_update_dfrac_alloc.
      {
        apply gmap_core_id.
        intros i x H.
        rewrite lookup_singleton_Some in H.
        destruct H as [<- <-].
        rewrite /CoreId /borrow_entry //.
      }
      apply singleton_included_l.
      exists (owner_entry n).
      rewrite lookup_fmap lookup_insert.
      split; first done.
      apply Some_included_mono.
      exists (owner_entry n).
      unfold owner_entry, borrow_entry.
      rewrite -pair_op -Some_op.
      split; cbn; trivial.
      by rewrite agree_idemp.
    }
  Qed.

  Lemma istate_read l σ :
    has_prngs σ
    -∗ known_prng l
    -∗ has_prngs σ ∗ ∃ n, (σ !! l) ≡ Some n.
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "%H".
    iFrame.
    rewrite /owner_store /borrow_store auth_both_valid_discrete in H.
    destruct H as [H _].
    apply singleton_included_l in H.
    destruct H as ([] & H1 & H2).
    rewrite lookup_fmap in H1.
    destruct (σ !! l) as [x|] eqn:Hlookup.
    - by iExists x.
    - rewrite Hlookup in H1.
      simpl in H1.
      inversion H1.
  Qed.

  Lemma istate_write l n' σ :
    has_prngs σ
    -∗ known_prng l
    ==∗ has_prngs (<[l:=n']> σ).
  Proof.
    iIntros "H #Hl".
    iPoseProof (istate_read l σ with "H Hl") as "(H & [%n %Hlookup])".
    iMod (own_update_2 with "H Hl") as "[$ _]"; last done.
    unfold owner_store, borrow_store.
    rewrite fmap_insert.
    apply auth_update.
    eapply singleton_local_update.
    - rewrite lookup_fmap Hlookup //.
    - unfold owner_entry, borrow_entry.
      apply prod_local_update; simpl.
  Admitted.

  Lemma wp_new_hom (k : locO -n> IT) s Φ `{!NonExpansive Φ} (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷▷ (∀ l, known_prng l -∗ WP@{rs} κ (k l) @ s {{ Φ }}) -∗
    WP@{rs} κ (PRNG_NEW k) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Ha".
    rewrite /PRNG_NEW hom_vis.
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
    iSplit; first rewrite later_map_Next ofe_iso_21 //.
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
    ▷▷ (∀ l, known_prng l -∗ WP@{rs} k l @ s {{ Φ }}) -∗
    WP@{rs} PRNG_NEW k @ s {{ Φ }}.
  Proof.
    iIntros "Hh H".
    iApply (wp_new_hom _ _ _ idfun with "Hh H").
  Qed.

  Lemma wp_gen_k_hom (l : loc) (cont : natO -n> IT) s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷ known_prng l -∗
    ▷▷ (known_prng l -∗ ∀ n : nat, WP@{rs} κ (cont n) @ s {{ Φ }}) -∗
    WP@{rs} κ (PRNG_GEN_k l cont) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx #Hp Ha".
    rewrite /PRNG_GEN_k hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iSimpl.
    iInv (nroot.@"prngE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iSimpl.
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    iPoseProof (istate_read l σ with "Hh Hp") as "(Hh & %m & %Hread)".
    (* current state, reification results, new state, continuation, thread pool additions *)
    iExists σ,(read_lcg m),(<[l:=update_lcg m]>σ),(κ (cont $ read_lcg m)),[].
    iFrame "Hs".
    iSplit; first rewrite /lift_post /state_gen Hread //.
    iSplit; first rewrite ofe_iso_21 later_map_Next //.
    iNext.
    iMod (istate_write l (update_lcg m) σ with "Hh Hp") as "Hh".
    iIntros "Hlc Hs".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "Hemp".
    { iExists _. iFrame. }
    iModIntro.
    iSplit.
    - iApply ("Ha" with "Hp").
    - by iFrame.
  Qed.

  Lemma wp_gen (l : loc) s Φ :
    prng_ctx -∗
    ▷ known_prng l -∗
    ▷▷ (known_prng l -∗ ∀ n : nat, Φ (RetV n)) -∗
    WP@{rs} PRNG_GEN l @ s {{ Φ }}.
  Proof.
    iIntros "#Hcxt Hp Ha".
    iApply (wp_gen_k_hom _ _ _ _ idfun with "Hcxt Hp").
    iIntros "!> !> Hl %n".
    iApply wp_val.
    iApply ("Ha" with "Hl").
  Qed.

  Lemma wp_seed_k_hom (l : loc) (cont : unitO -n> IT) m s Φ (κ : IT -n> IT) `{!IT_hom κ} :
    prng_ctx -∗
    ▷ known_prng l -∗
    ▷▷ (known_prng l -∗ WP@{rs} κ (cont ()) @ s {{ Φ }}) -∗
    WP@{rs} κ (PRNG_SEED_k l m cont) @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx #Hp Ha".
    rewrite /PRNG_SEED_k hom_vis.
    iApply wp_subreify_ctx_indep_lift''.
    iInv (nroot.@"prngE") as (σ) "[>Hlc [Hs Hh]]" "Hcl".
    iSimpl.
    iApply (lc_fupd_elim_later with "Hlc").
    iNext.
    (* current state, reification results, new state, continuation, thread pool additions *)
    iExists σ,(),(<[l:=m]>σ),(κ (cont ())),[].
    iFrame "Hs".
    iSplit.
    {
      iPoseProof (istate_read l σ with "Hh Hp") as "(Hh & %mm & %Hread)".
      rewrite /lift_post /state_seed Hread //.
    }
    iSplit; first rewrite ofe_iso_21 later_map_Next //.
    iNext.
    iMod (istate_write l m σ with "Hh Hp") as "Hh".
    iIntros "Hlc Hs".
    iMod ("Hcl" with "[Hlc Hh Hs]") as "Hemp".
    { iExists _. iFrame. }
    iModIntro.
    iSplit.
    - by iApply "Ha".
    - by iFrame.
  Qed.

  Lemma wp_seed (l : loc) m s Φ :
    prng_ctx -∗
    ▷ known_prng l -∗
    ▷▷ (known_prng l -∗ Φ (RetV ())) -∗
    WP@{rs} PRNG_SEED l m @ s {{ Φ }}.
  Proof.
    iIntros "#Hctx Hp Ha".
    iApply (wp_seed_k_hom l _ _ _ _ idfun with "Hctx Hp [Ha]").
    do 2 iNext.
    iIntros "H".
    iDestruct ("Ha" with "H") as "G".
    iApply wp_val.
    by iModIntro.
  Qed.

End wp.

Arguments prng_ctx {_ _} rs {_ _ _ _ _ _}.
Arguments known_prng {_ _} _.
#[global] Opaque PRNG_NEW PRNG_DEL_k PRNG_GEN_k PRNG_SEED_k.

