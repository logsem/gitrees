From iris.algebra Require Import excl auth frac agree gmap list gmap_view.
From iris.algebra.lib Require Import excl_auth.
From iris.proofmode Require Import base tactics classes modality_instances.
From iris.base_logic.lib Require Export own fancy_updates invariants.
From gitrees Require Import prelude.
From gitrees.gitree Require Import core reify greifiers reductions weakestpre.
From gitrees Require Import hom.

(* Section Fib. *)
(*   Context {Σ : gFunctor}. *)
(*   Notation iProp := (iProp Σ). *)

(*   Record fib_ob := *)
(*     MkFibOb { *)
(*         fib_carrier :> ofe; *)
(*         fib_carrier_cofe : Cofe fib_carrier; *)
(*         fib_pred : fib_carrier -n> iProp; *)
(*       }. *)

(*   Record fib_arr (X Y : fib_ob) := *)
(*     MkFibArr { *)
(*         fib_arr_carrier :> X -n> Y; *)
(*         fib_arr_closed : ⊢ ∀ x, fib_pred X x -∗ fib_pred Y (fib_arr_carrier x); *)
(*       }. *)
(*   Arguments fib_arr_carrier {_ _}. *)

(*   Local Instance fib_arr_equiv {X Y} : Equiv (fib_arr X Y) := *)
(*     λ f g, f ≡ g. *)

(*   Local Instance fib_arr_dist {X Y} : Dist (fib_arr X Y) := *)
(*     λ n f g, f ≡{n}≡ g. *)

(*   Definition fib_arr_ofe_mixin {X Y} : OfeMixin (fib_arr X Y). *)
(*   Proof. *)
(*     split. *)
(*     - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|]. *)
(*       intros H. by apply equiv_dist. *)
(*     - intros n; split. *)
(*       + by intros f x. *)
(*       + by intros f g ? x. *)
(*       + intros f g h H G x. *)
(*         by trans (fib_arr_carrier g x). *)
(*     - intros n m f g ? x ?; eauto using dist_le with si_solver. *)
(*   Qed. *)
(*   Canonical Structure fib_arrO {X Y} := Ofe (fib_arr X Y) fib_arr_ofe_mixin. *)

(*   Program Definition fib_arr_id {X : fib_ob} : fib_arr X X *)
(*     := MkFibArr X X idfun _. *)

(*   Program Definition fib_arr_comp {X Y Z : fib_ob} : fib_arr Y Z → fib_arr X Y → fib_arr X Z *)
(*     := λ f g, MkFibArr X Z (λne x, fib_arr_carrier f (fib_arr_carrier g x)) _. *)
(*   Next Obligation. *)
(*     intros ?? H. *)
(*     solve_proper. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     iIntros (x) "H". *)
(*     by do 2 iApply fib_arr_closed. *)
(*   Qed. *)

(*   Lemma fib_arr_comp_id_left {X Y} (f : fib_arr X Y) : *)
(*     fib_arr_comp fib_arr_id f ≡ f. *)
(*   Proof. by intros x. Qed. *)

(*   Lemma fib_arr_comp_id_right {X Y} (f : fib_arr X Y) : *)
(*     fib_arr_comp f fib_arr_id ≡ f. *)
(*   Proof. by intros x. Qed. *)

(*   Lemma fib_arr_comp_id_assoc {X Y Z W} *)
(*     (f : fib_arr X Y) (g : fib_arr Y Z) (h : fib_arr Z W) : *)
(*     fib_arr_comp h (fib_arr_comp g f) ≡ fib_arr_comp (fib_arr_comp h g) f. *)
(*   Proof. by intros x. Qed. *)

(*   Record functor *)
(*     := MkFunctor { *)
(*            functor_car : fib_ob → { o : ofe & Cofe o }; *)
(*            functor_map : ∀ {X Y : fib_ob}, *)
(*              fib_arr X Y → projT1 (functor_car X) -n> projT1 (functor_car Y); *)
(*            functor_map_id : ∀ X, functor_map (@fib_arr_id X) ≡ idfun; *)
(*            functor_map_comp : ∀ {X Y Z} (f : fib_arr Y Z) (g : fib_arr X Y), *)
(*              functor_map (fib_arr_comp f g) ≡ ccompose (functor_map f) (functor_map g); *)
(*     }. *)

(*   Program Definition forget : functor := *)
(*     MkFunctor (λ x, existT (fib_carrier x) (fib_carrier_cofe x)) *)
(*       (λ _ _ f, fib_arr_carrier f) *)
(*       _ *)
(*       _. *)
(*   Next Obligation. *)
(*     by intros ?; simpl. *)
(*   Qed.   *)
(* End Fib. *)


Section functors.
  Inductive poly : oFunctor → Prop :=
  | id_poly : poly idOF
  | prod_poly {F G} : poly F → poly G → poly (prodOF F G)
  | sum_poly {F G} : poly F → poly G → poly (sumOF F G)
  | exp_poly {F G} : poly F → poly G → poly (ofe_morOF F G).

  Inductive liftable : oFunctor → Prop :=
  | later_liftable {F} : poly F → liftable (laterOF F)
  | const_liftable {A} : liftable (constOF A)
  | prod_liftable {F G} : liftable F → liftable G → liftable (prodOF F G)
  | sum_liftable {F G} : liftable F → liftable G → liftable (sumOF F G)
  | exp_liftable {F G} : liftable F → liftable G → liftable (ofe_morOF F G)
  | sig_liftable {B} (H : B → oFunctor) : (∀ b, liftable (H b)) → liftable (sigTOF H).

  Context {Σ : opsInterp}.
  Context {Σ_lift_ins : ∀ i, liftable (Ins (opsInterp_lookup Σ i))}.
  Context {Σ_lift_outs : ∀ i, liftable (Outs (opsInterp_lookup Σ i))}.
  Context {A : ofe}.

  Lemma ITOF_liftable : liftable (IT_pre.ITOF Σ A).
  Proof using A Σ Σ_lift_ins Σ_lift_outs.
    constructor.
    - repeat constructor.
    - constructor.
      intros.
      constructor.
      + apply Σ_lift_ins.
      + constructor.
        * apply Σ_lift_outs.
        * repeat constructor.
  Qed.
End functors.

Definition specN := nroot .@ "spec".

Lemma take_drop_middle_L :
  ∀ {A : ofe} (l : list A) (i : nat) (x : A),
  l !! i ≡ Some x → take i l ++ x :: drop (S i) l ≡ l.
Proof.
  intros A l.
  induction l as [| x l Hl].
  - intros ?? H; simpl.
    exfalso.
    rewrite lookup_nil in H.
    inversion H.
  - intros i y H.
    simpl.
    destruct i as [| i].
    + simpl.
      rewrite drop_0.
      simpl in H.
      inversion H; subst.
      f_equiv; by symmetry.
    + simpl.
      f_equiv.
      simpl in H.
      by apply (Hl i y).
Qed.

Lemma lookup_lt_Some_L : ∀ {A : ofe} (l : list A) (i : nat) (x : A),
  l !! i ≡ Some x → i < length l.
Proof.
  intros ? l.
  induction l as [| y l Hl]; intros G.
  - intros ? J; inversion J.
  - intros x J.
    simpl.
    destruct G as [| G].
    + simpl in J.
      lia.
    + apply Arith_prebase.lt_n_S_stt.
      eapply Hl.
      apply J.
Qed.

Lemma lookup_geq_None_L : ∀ {A : ofe} (l : list A) (i : nat),
  l !! i ≡ None → i ≥ length l.
Proof.
  intros ? l.
  induction l as [| y l Hl]; intros G.
  - intros J; inversion J.
    simpl.
    lia.
  - intros J.
    simpl.
    destruct G as [| G].
    + simpl in J.
      inversion J.
    + simpl in J.
      apply Hl in J.
      lia.
Qed.

Lemma lookup_geq_None_L_inv : ∀ {A : ofe} (l : list A) (i : nat),
  i ≥ length l → l !! i = None.
Proof.
  intros ? l.
  induction l as [| y l Hl]; intros G.
  - intros J.
    done.
  - intros J.
    simpl in J.
    assert (∃ G', G = S G') as [G' ->].
    {
      inversion J as [ | J'].
      - exists (length l).
        lia.
      - exists J'.
        lia.
    }
    simpl.
    apply Hl.
    lia.
Qed.

Section tp.
  Context {n : nat} {a : is_ctx_dep} (rs : gReifiers a n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Definition tpoolUR : ucmra := gmap_viewR nat (agreeR IT).

  Fixpoint to_tpool_go (i : nat) (tp : listO IT) : gmap nat (agreeR IT) :=
    match tp with
    | [] => ∅
    | e :: tp => <[i:=to_agree e]>(to_tpool_go (S i) tp)
    end.

  Lemma to_tpool_go_lookup (tp : listO IT) i :
    ∀ k j, to_tpool_go k tp !! j = to_tpool_go (k + i) tp !! (j + i).
  Proof.
    revert i.
    induction tp as [| ? tp IH].
    - done.
    - simpl.
      intros i k j.
      destruct (decide (k = j)); [subst |].
      + by rewrite !lookup_insert.
      + rewrite lookup_insert_ne; last done.
        rewrite (IH i (S k) j) /=.
        rewrite lookup_insert_ne; last lia.
        reflexivity.
  Qed.

  Lemma to_tpool_go_lookup' (tp : listO IT) :
    ∀ j k, to_agree <$> tp !! j = to_tpool_go k tp !! (k + j).
  Proof.
    induction tp as [| x tp IH].
    - intros ?; simpl.
      done.
    - intros j; simpl.
      destruct j as [| j].
      + simpl.
        intros k.
        rewrite Nat.add_0_r.
        destruct (decide (k = 0)); [subst |].
        * by rewrite lookup_insert.
        * by rewrite lookup_insert.
      + simpl.
        intros k.
        rewrite lookup_insert_ne; last lia.
        rewrite -Nat.add_succ_comm.
        rewrite -IH.
        reflexivity.
  Qed.

  Lemma to_tpool_go_comm_insert (tp : listO IT) j (H : j < length tp) x :
    to_tpool_go 0 (<[j := x]> tp) = <[j := to_agree x]> (to_tpool_go 0 tp).
  Proof.
    apply map_eq.
    intros q.
    rewrite -!(to_tpool_go_lookup' _ _ 0).
    destruct (decide (j = q)); [subst |].
    - rewrite lookup_insert.
      by rewrite list_lookup_insert; last done.
    - rewrite list_lookup_insert_ne; last done.
      rewrite lookup_insert_ne; last done.
      by rewrite (to_tpool_go_lookup' _ _ 0).
  Qed.

  Lemma to_tpool_go_comm_union (tp tp' : listO IT) :
    ∀ k, to_tpool_go k (tp ++ tp') = (to_tpool_go k tp) ∪ (to_tpool_go (k + length tp) tp').
  Proof.
    revert tp'.
    induction tp as [| ? ? IH].
    - intros; simpl.
      symmetry.
      rewrite Nat.add_0_r.
      apply (map_empty_union (to_tpool_go k tp')).
    - intros tp' k.
      rewrite /= IH Nat.add_succ_comm.
      by rewrite insert_union_l.
  Qed.

  Lemma to_tpool_go_map_to_list (tp : listO IT) :
    ∀ k, (map_to_list (to_tpool_go k tp)) ≡ₚ (zip (seq k (length tp)) (to_agree <$> tp)).
  Proof.
    induction tp as [| ? ? IH].
    - done.
    - intros k.
      rewrite /= -IH.
      rewrite map_to_list_insert; first done.
      replace (S k) with (1 + k) by reflexivity.
      assert (1 + k > k) as H; first lia.
      revert H.
      generalize (1 + k).
      generalize k.
      clear.
      induction tp as [| ? ? IH]; intros k p H.
      + done.
      + intros.
        rewrite /= lookup_insert_ne; last lia.
        apply IH; lia.
  Qed.

  Program Definition to_tpool' : listO IT -> tpoolUR := λ l, ●V (to_tpool_go 0 l).

  Program Definition to_tpool : listO IT -n> tpoolUR := λne l, (to_tpool' l).
  Next Obligation.
    rewrite /to_tpool'.
    intros m.
    intros l.
    revert m.
    generalize 0.
    induction l as [| x l Hl]; intros p m ? H.
    - apply Forall2_nil_inv_l in H.
      rewrite H.
      reflexivity.
    - apply Forall2_cons_inv_l in H.
      destruct H as [x' [l' [H1 [H2 H3]]]].
      rewrite H3.
      simpl.
      do 2 f_equiv.
      + solve_proper.
      + specialize (Hl (S p) m l' H2).
        destruct Hl as [Hl _].
        simpl in Hl.
        apply Some_dist_inj in Hl.
        apply pair_dist_inj in Hl.
        destruct Hl as [_ Hl].
        apply to_agree_injN in Hl.
        apply Hl.
  Qed.

  Class tpoolSG Σ := TPOOLSG { tpool_inG :: inG Σ (tpoolUR); tpool_name : gname }.
End tp.

Section rel.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ} `{!tpoolSG rs R Σ} `{!stateG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Lemma IT_tau_err_ne' α e :
    (Tau (A := R) (E := F) α ≡ Err e → False).
  Proof.
    intros H1.
    assert (IT_unfold (Tau α) ≡ IT_unfold (Err e)) as H2.
    { by rewrite H1. }
    rewrite !IT_unfold_fold /= in H2.
    inversion H2 as [?? G |]; subst.
    inversion G.
  Qed.

  Transparent Tau.
  Lemma Tau_inj'' (α β : laterO IT) :
    ((Tau α ≡ Tau β) → α ≡ β).
  Proof.
    intros H.
    assert ((IT_unfold (Tau α)) ≡ (IT_unfold (Tau β))) as G.
    { rewrite H. done. }
    unfold Tau in G. simpl in G.
    rewrite !IT_unfold_fold in G.
    inversion G as [?? J |]; subst.
    inversion J; subst.
    done.
  Qed.
  Opaque Tau.

  Lemma reify_vis_cont op i k1 k2 σ1 σ2 β th :
    (reify (A := R) (gReifiers_sReifier rs) (Vis op i k1) σ1 ≡
       (σ2, Tick β, th) →
     reify (gReifiers_sReifier rs) (Vis op i (laterO_map k2 ◎ k1)) σ1 ≡
       (σ2, Tick (k2 β), th)).
  Proof.
    destruct (sReifier_re (gReifiers_sReifier rs) op (i,σ1))
      as [[[o σ2'] th']|] eqn:Hre; last first.
    - rewrite reify_vis_None_ctx_indep; last by rewrite Hre//.
      intros Hr.
      exfalso.
      destruct Hr as [[_ Hr2] _].
      simpl in Hr2.
      symmetry in Hr2.
      by apply IT_tau_err_ne' in Hr2.
    - rewrite reify_vis_eq_ctx_indep; last first.
      { by rewrite Hre. }
      rewrite reify_vis_eq_ctx_indep; last first.
      { by rewrite Hre. }
      intros Hr.
      destruct Hr as [[Hr1 Hr2] Hr3].
      simpl in *.
      rewrite Tick_eq in Hr2.
      rewrite Hr1.
      rewrite -Hr3.
      do 2 f_equiv.
      apply Tau_inj'' in Hr2.
      rewrite Hr2.
      rewrite later_map_Next.
      reflexivity.
  Qed.

  Lemma external_step_ectx (K : HOM) e e' σ σ' efs :
    external_step (gReifiers_sReifier rs) e σ e' σ' efs
    → external_step (gReifiers_sReifier rs) (K e) σ (K e') σ' efs.
  Proof.
    intros H.
    destruct H as [???? H1 H2 | ???????? H1 H2].
    - rewrite H1 H2.
      rewrite hom_tick.
      by constructor.
    - rewrite H1.
      rewrite hom_vis.
      econstructor.
      + reflexivity.
      + assert (reify (gReifiers_sReifier rs) (Vis op i k) σ1 ≡ (σ2, Tick β, th))
          as J.
        {
          rewrite -H2.
          do 2 f_equiv.
          symmetry.
          done.
        }
        pose proof (reify_vis_cont op i k (λne x, K x) σ1 σ2 β th J) as L.
        simpl in J.
        rewrite -L.
        do 3 f_equiv.
        intros ?.
        reflexivity.
  Qed.

  Program Definition tpool_pointsto (j : natO) (e : IT) : iProp :=
    own (tpool_name rs R) (gmap_view_frag j (DfracOwn 1) (to_agree e)).

  Global Instance tpool_pointsto_ne l : NonExpansive (tpool_pointsto l).
  Proof.
    intros ??? H.
    rewrite /tpool_pointsto.
    do 3 f_equiv.
    done.
  Qed.

  Global Instance tpool_pointsto_proper l : Proper ((≡) ==> (≡)) (tpool_pointsto l).
  Proof.
    intros ?? H.
    rewrite /tpool_pointsto.
    do 3 f_equiv.
    apply H.
  Qed.

  Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.

  Program Definition spec_inv (ρ : listO IT) σ : iProp :=
    (∃ tp σ' m, own (tpool_name rs R) ((to_tpool rs R tp))
                ∗ state_interp σ'
                ∗ tp_internal_steps (gReifiers_sReifier rs) ρ σ tp σ' m)%I.

  Definition spec_ctx : iProp :=
    (∃ ρ σ, inv specN (spec_inv ρ σ))%I.

  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.

  Lemma step_insert (K : HOM) (tp : listO IT) j e σ e' σ' efs :
    tp !! j ≡ Some (K e) → external_step (gReifiers_sReifier rs) e σ e' σ' efs →
    tp_external_step (gReifiers_sReifier rs) tp σ (<[j:=K e']> tp ++ efs) σ'.
  Proof.
    intros.
    rewrite -(take_drop_middle_L tp j (K e)) //.
    rewrite insert_app_r_alt; first last.
    {
      rewrite take_length_le; first reflexivity.
      apply Nat.lt_le_incl.
      eapply lookup_lt_Some_L; eassumption.
    }
    econstructor.
    - reflexivity.
    - rewrite -assoc_L.
      f_equiv.
      rewrite take_length_le; first last.
      {
        apply Nat.lt_le_incl.
        eapply lookup_lt_Some_L.
        eassumption.
      }
      rewrite Nat.sub_diag.
      simpl.
      reflexivity.
    - by apply external_step_ectx.
  Qed.

  Lemma step_insert_no_fork (K : HOM) (tp : listO IT) j e σ e' σ' :
    tp !! j ≡ Some (K e) → external_step (gReifiers_sReifier rs) e σ e' σ' [] →
    tp_external_step (gReifiers_sReifier rs) tp σ (<[j:=K e']> tp) σ'.
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma tp_external_steps_many' (α1 : listO IT) σ1 α2 σ2 α3 σ3 n2 :
    tp_external_step (gReifiers_sReifier rs) α2 σ2 α3 σ3 →
    tp_external_steps (gReifiers_sReifier rs) α1 σ1 α2 σ2 n2 →
    tp_external_steps (gReifiers_sReifier rs) α1 σ1 α3 σ3 (S n2).
  Proof.
    intros G H; revert G.
    induction H as [| ????????? IH]; intros G.
    - setoid_subst.
      econstructor; last constructor; first apply G; done.
    - by econstructor; last by apply IH; done.
  Qed.

  Lemma tp_internal_steps_many' (α1 : listO IT) σ1 α2 σ2 α3 σ3 n2 :
    ⊢ tp_internal_step (Σ := Σ) (gReifiers_sReifier rs) α2 σ2 α3 σ3
      -∗ tp_internal_steps (gReifiers_sReifier rs) α1 σ1 α2 σ2 n2
      -∗ tp_internal_steps (gReifiers_sReifier rs) α1 σ1 α3 σ3 (S n2).
  Proof.
    iRevert (α1 σ1 α2 σ2 α3 σ3 n2).
    iLöb as "IH".
    iIntros (α1 σ1 α2 σ2 α3 σ3 n2).
    iIntros "G H"; iRevert "G".
    iEval (rewrite tp_internal_steps_unfold) in "H".
    iDestruct "H" as "[(-> & H) | H]".
    - iDestruct "H" as "(H1 & H2)".
      iRewrite "H1". iRewrite "H2".
      iIntros "G".
      iEval (rewrite tp_internal_steps_unfold).
      iRight.
      iExists 0, α3, σ3.
      iSplit; first done.
      iSplit; first done.
      iNext.
      iEval (rewrite tp_internal_steps_unfold).
      by iLeft.
    - iDestruct "H" as "(%n' & %γ & %σ' & #H1 & #H2 & #H3)".
      iIntros "#G".
      iEval (rewrite tp_internal_steps_unfold).
      iRight.
      iExists (S n'), γ, σ'.
      iSplit; first by iRewrite "H1".
      iSplit; first done.
      iNext.
      iApply "IH".
      + iApply "G".
      + iApply "H3".
  Qed.

  Lemma tpool_read l α tp :
    own (tpool_name rs R) (to_tpool rs R tp)
    -∗ tpool_pointsto l α
    -∗ (tp !! l) ≡ Some α.
  Proof.
    iIntros "Ha Hf".
    iPoseProof (own_valid_2 with "Ha Hf") as "H".
    rewrite gmap_view_both_validI.
    iDestruct "H" as "[%H Hval]".
    rewrite option_equivI.
    rewrite -(to_tpool_go_lookup' rs R tp l 0).
    destruct (tp !! l) as [o |] eqn:Heq.
    - rewrite Heq /=.
      rewrite agree_equivI.
      by iRewrite "Hval".
    - rewrite Heq /=.
      done.
  Qed.

  Lemma tpool_alloc α l σ :
    σ !! l = None →
    own (tpool_name rs R) (to_tpool rs R σ)
    ==∗ own (tpool_name rs R) (●V (<[l:=to_agree (α)]>(to_tpool_go rs R 0 σ)))
                   ∗ tpool_pointsto l α.
  Proof.
    iIntros (Hl) "H".
    iMod (own_update with "H") as "[$ $]".
    { apply (gmap_view_alloc _ l (DfracOwn 1) (to_agree (α))); eauto.
      - rewrite -(to_tpool_go_lookup' rs R σ l 0).
        by rewrite Hl.
      - done.
    }
    done.
  Qed.

  Lemma tpool_alloc_big (α : listO IT) σ :
    own (tpool_name rs R) (to_tpool rs R σ)
    ==∗ own (tpool_name rs R)
          (●V ((to_tpool_go rs R 0 σ) ∪ (to_tpool_go rs R (length σ) α)))
                   ∗ [∗ list] i ∈ α, ∃ j, tpool_pointsto j i.
  Proof.
    iIntros "H".
    assert (∀ k, to_tpool_go rs R (k + (length σ)) α ##ₘ to_tpool_go rs R k σ) as HD.
    {
      induction σ as [| x σ IH].
      - intros; apply map_disjoint_empty_r.
      - intros k; simpl.
        apply map_disjoint_insert_r_2.
        + rewrite Nat.add_comm.
          rewrite -(to_tpool_go_lookup rs R α k (S (length σ)) 0).
          clear.
          generalize (length σ).
          induction α as [| ? ? IH].
          * done.
          * intros m; simpl.
            rewrite lookup_insert_ne; last done.
            apply IH.
        + rewrite -Nat.add_1_l Nat.add_assoc (Nat.add_comm k).
          apply IH.
    }
    iMod (own_update with "H") as "[H1 H2]".
    {
      specialize (HD 0).
      simpl in HD.
      apply (gmap_view_alloc_big (to_tpool_go rs R 0 σ)
                     (to_tpool_go rs R (length σ) α)
                     (DfracOwn 1) HD); eauto.
      done.
    }
    rewrite map_union_comm; last apply (HD 0).
    iModIntro.
    iSplitL "H1".
    - unfold gmap_view_auth. (* wtf ??? *)
      iFrame "H1".
    - unfold tpool_pointsto.
      clear.
      generalize (length σ).
      intros p.
      iInduction α as [| ??] "IH" forall (p).
      + done.
      + simpl.
        rewrite big_opM_insert.
        * iDestruct "H2" as "(H2 & H3)".
          iSplitL "H2".
          -- by iExists p.
          -- iApply "IH".
             iApply "H3".
        * replace (S p) with (1 + p) by reflexivity.
          assert (1 + p > p) as H; first lia.
          revert H.
          generalize (1 + p).
          generalize p.
          clear.
          induction α as [| ? ? IH]; intros k p H.
          -- done.
          -- intros.
             rewrite /= lookup_insert_ne; last lia.
             apply IH; lia.
  Qed.

  Lemma tpool_loc_dom l α tp :
    own (tpool_name rs R) (to_tpool rs R tp)
    -∗ tpool_pointsto l α -∗ ⌜is_Some (tp !! l)⌝.
  Proof.
    iIntros "Hinv Hloc".
    iPoseProof (tpool_read with "Hinv Hloc") as "Hl".
    destruct (tp !! l) ; eauto.
    by rewrite option_equivI.
  Qed.

  Lemma tpool_write l α β σ :
    own (tpool_name rs R) (to_tpool rs R σ)
    -∗ tpool_pointsto l α
    ==∗ own (tpool_name rs R) (●V <[l:=(to_agree (β))]>(to_tpool_go rs R 0 σ))
      ∗ tpool_pointsto l β.
  Proof.
    iIntros "H Hl".
    iMod (own_update_2 with "H Hl") as "[$ $]"; last done.
    apply gmap_view_update.
  Qed.

  (* generalize to arbitrary internal steps + new treads *)
  Lemma step_tick `{!Inhabited (gReifiers_state rs ♯ IT)} E j e :
    nclose specN ⊆ E →
    £ 1 ∗ spec_ctx ∗ (▷ j ⤇ Tick e) ={E}=∗ j ⤇ e.
  Proof.
    iIntros (HSub) "[HCred [#HSpec HPt]]".
    iDestruct "HSpec" as (tp σ) "HSpec".
    iInv specN as (tp' σ' m) "[H [HS #HStep]]" "HClose".
    iApply (lc_fupd_add_later with "HCred").
    iNext.
    iAssert (⌜is_Some (tp' !! j)⌝)%I as "%Hdom".
    { iApply (tpool_loc_dom with "H HPt"). }
    destruct Hdom as [x Hx].
    iAssert ((tp' !! j ≡ Some (Tick e)))%I as "#Hlookup".
    { iApply (tpool_read with "H HPt"). }
    iMod (tpool_write _ _ e with "H HPt") as "[Hh Hp]".
    iMod ("HClose" with "[HS Hh]") as "_"; last by iModIntro.
    iNext.
    iExists (<[j:=e]> tp'), σ', (S m).
    iFrame "HS".
    iSplit; first last.
    - iApply tp_internal_steps_many'; last done.
      unshelve epose proof (take_drop_middle tp' j x _) as H; first by rewrite Hx.
      rewrite -H.
      rewrite list_lookup_middle; first last.
      {
        rewrite take_length_le; first done.
        eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
      }
      iDestruct (option_equivI with "Hlookup") as "G".
      iRewrite "G".
      iExists (take j tp'), (drop (S j) tp'), (Tick e), e, [].
      iSplit; first done.
      iSplit.
      {
        rewrite insert_app_r_alt; last (rewrite take_length; lia).
        rewrite app_nil_r.
        iApply f_equivI.
        assert (j - length (take j tp') = 0) as ->.
        {
          rewrite take_length_le; first lia.
          eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
        }
        simpl.
        done.
      }
      iLeft.
      done.
    - rewrite /to_tpool /= /to_tpool'.
      rewrite to_tpool_go_comm_insert; first done.
      eapply lookup_lt_Some; eassumption.
  Qed.

  (* need to bake state into spec_ctx *)
  Lemma step_reify `{!Inhabited (gReifiers_state rs ♯ IT)}
    `{subR : !subReifier sR rs}
    E j
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l :
    nclose specN ⊆ E →
    £ 1
    ∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
    ∗ k (subEff_outs y) ≡ Next β
    ∗ spec_ctx
    ∗ ▷ has_substate σ
    ∗ ▷ j ⤇ (Vis (subEff_opid op) (subEff_ins x) k)
    ={E}=∗ j ⤇ β
         ∗ ([∗ list] i ∈ listO_map Tau l, ∃ k : natO, k ⤇ i)
         ∗ has_substate σ'.
  Proof.
    iIntros (HSub) "(HCred & #Hr & #HEq & #HSpec & HSt & HPt)".
    iDestruct "HSpec" as (tp σ'') "HSpec".
    iInv specN as (tp' σ''' m) "[H [HS #HStep]]" "HClose".
    iApply (lc_fupd_add_later with "HCred").
    iNext.
    iAssert (⌜is_Some (tp' !! j)⌝)%I as "%Hdom".
    { iApply (tpool_loc_dom with "H HPt"). }
    destruct Hdom as [x' Hx].
    iAssert ((tp' !! j ≡ Some (Vis (subEff_opid op) (subEff_ins x) k)))%I
      as "#Hlookup".
    { iApply (tpool_read with "H HPt"). }
    iMod (tpool_write _ _ β
           with "H HPt") as "[Hh Hp]".
    iMod (tpool_alloc_big (listO_map Tau l) (<[j := β]>tp') with "[Hh]") as "[Hh Hpool]".
    {
      rewrite /to_tpool /to_tpool' /=.
      rewrite to_tpool_go_comm_insert; first done.
      apply lookup_lt_is_Some_1.
      eexists _; eassumption.
    }
    destruct (gState_decomp sR_idx σ''') as [a rest] eqn:Hdecomp.
    assert (σ''' ≡ gState_recomp rest a) as Hfs.
    { symmetry. apply gState_recomp_decomp. by rewrite Hdecomp. }
    iAssert (a ≡ (sR_state σ))%I with "[HS HSt]" as "#Hss".
    {
      iEval (rewrite Hfs) in "HS".
      iApply (state_interp_has_state_idx_agree with "HS HSt").
    }
    iAssert (internal_step (gReifiers_sReifier rs)
               ((Vis (subEff_opid op) (subEff_ins x) k)) σ'''
               β (gState_recomp rest (sR_state σ')) (listO_map Tau l)) as "HStep'".
    {
      iRight.
      iExists (subEff_opid op), (subEff_ins x), k.
      iSplit; first done.
      rewrite Tick_eq.
      iDestruct (reify_vis_eqI_ctx_indep rs
                     (subEff_opid op) (subEff_ins x) k
                     (subEff_outs y) (gState_recomp rest (sR_state σ))
                     (gState_recomp rest (sR_state σ')) l
                  with "[]") as "Hreify".
      {
        iApply subReifier_reifyI_ctx_indep.
        iApply "Hr".
      }
      iRewrite "HEq" in "Hreify".
      setoid_replace σ''' with (gState_recomp rest a); last done.
      iRewrite "Hss".
      iApply "Hreify".
    }
    iEval (rewrite Hfs) in "HS".
    iMod (state_interp_has_state_idx_update _ (sR_state σ') with "HS HSt") as "[HS HSt]".
    iFrame "Hp Hpool HSt".
    iApply "HClose".
    iNext.
    iExists (<[j := β]>tp' ++ (listO_map Tau l)),
      (gState_recomp rest (sR_state σ')), (S m).
    iSplitL "Hh".
    - rewrite /to_tpool /to_tpool'.
      rewrite -to_tpool_go_comm_union /=.
      iFrame "Hh".
    - iFrame "HS".
      iApply tp_internal_steps_many'; last done.
      unshelve epose proof (take_drop_middle tp' j x' _) as H; first done.
      rewrite -H; clear H.
      rewrite list_lookup_middle; first last.
      {
        rewrite take_length_le; first done.
        eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
      }
      iDestruct (option_equivI with "Hlookup") as "G".
      iRewrite "G"; iClear "G".

      iExists (take j tp'), (drop (S j) tp'), (Vis (subEff_opid op) (subEff_ins x) k), (β), (listO_map Tau l).
      iSplit; first done.
      iSplit.
      {
        rewrite insert_app_r_alt; last (rewrite take_length; lia).
        rewrite -app_assoc.
        iApply f_equivI.
        assert (j - length (take j tp') = 0) as ->.
        {
          rewrite take_length_le; first lia.
          eapply Nat.lt_le_incl, lookup_lt_Some; eassumption.
        }
        simpl.
        done.
      }
      iApply "HStep'".
  Qed.

  Lemma step_reify_hom `{!Inhabited (gReifiers_state rs ♯ IT)}
    `{subR : !subReifier sR rs}
    (K : HOM) E j
    (op : opid (sReifier_ops sR))
    (x : Ins (sReifier_ops sR op) ♯ IT)
    (y : Outs (sReifier_ops sR op) ♯ IT)
    (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT)
    (σ σ' : sReifier_state sR ♯ IT) β l :
    nclose specN ⊆ E →
    £ 1
    ∗ sReifier_re sR op (x, σ) ≡ Some (y, σ', l)
    ∗ k (subEff_outs y) ≡ Next β
    ∗ spec_ctx
    ∗ ▷ has_substate σ
    ∗ ▷ j ⤇ K (Vis (subEff_opid op) (subEff_ins x) k)
    ={E}=∗ j ⤇ K β
         ∗ ([∗ list] i ∈ listO_map Tau l, ∃ k : natO, k ⤇ i)
         ∗ has_substate σ'.
  Proof.
    iIntros (HSub) "(HCred & #Hr & #HEq & #HSpec & HSt & HPt)".
    rewrite hom_vis.
    iDestruct (step_reify with "[Hr HEq $HSpec $HCred $HSt HPt]") as "H";
      first done.
    - iFrame "HPt".
      iFrame "Hr".
      rewrite /=.
      iRewrite "HEq".
      rewrite later_map_Next.
      done.
    - iApply "H".
  Qed.

  Program Definition IT_Rel_pre
    (IT_Val_Rel : ITV -n> ITV -n> iProp)
    : IT -n> IT -n> iProp
    := λne x y,
      (∀ j (K : HOM), j ⤇ K y
              -∗ WP@{rs} x @ s {{ v,
                       ∃ v', j ⤇ K (IT_of_V v')
                             ∗ IT_Val_Rel v v' }})%I.
  Next Obligation.
    intros ????? H1.
    do 2 (f_equiv; intros ?).
    do 3 f_equiv.
    done.
  Qed.
  Next Obligation.
    intros ???? H ?.
    simpl.
    do 2 (f_equiv; intros ?).
    do 2 f_equiv.
    solve_proper.
  Qed.

  Global Instance IT_Rel_pre_ne : NonExpansive IT_Rel_pre.
  Proof.
    intros ??? H.
    rewrite /IT_Rel_pre.
    intros ?; simpl.
    intros ?; simpl.
    do 2 (f_equiv; intros ?).
    do 2 f_equiv.
    intros ?; simpl.
    f_equiv; intros ?.
    f_equiv.
    solve_proper.
  Qed.

  Global Instance IT_Rel_pre_proper : Proper ((≡) ==> (≡) ==> (≡)) IT_Rel_pre.
  Proof.
    intros ?? H ?? G.
    rewrite /IT_Rel_pre.
    intros ?; simpl.
    do 2 (f_equiv; intros ?).
    do 2 f_equiv; first solve_proper.
    intros ?; simpl.
    f_equiv; intros ?.
    f_equiv.
    solve_proper.
  Qed.

  Program Definition IT_Val_Rel_pre :
    (ITV -n> ITV -n> iProp) -n> ITV -n> ITV -n> iProp
    := λne R x y,
      ((∃ a b, x ≡ RetV a ∧ y ≡ RetV b ∧ a ≡ b)
       ∨ (∃ m f g, x ≡ FunV (Next f) ∧ y ≡ FunV (Next g)
                 ∧ later_credits.lc_supply m
                 ∧ □ ∀ v w, ▷ (R v w
                               -∗ £ (n + 1)
                               -∗ IT_Rel_pre R
                                    (f (IT_of_V v)) (g (IT_of_V w)))))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    intros ??? H ??; simpl.
    f_equiv.
    do 3 (f_equiv; intros ?).
    do 4 f_equiv.
    do 2 (f_equiv; intros ?).
    do 2 f_equiv.
    - solve_proper.
    - f_equiv.
      do 2 (f_equiv; intros ?).
      do 2 f_equiv.
      intros ?; simpl.
      f_equiv; intros ?.
      f_equiv.
      solve_proper.
  Qed.

  Global Instance IT_Val_Rel_contractive : Contractive IT_Val_Rel_pre.
  Proof.
    intros m ?? H.
    rewrite /IT_Val_Rel_pre.
    intros ??; simpl.
    f_equiv.
    do 3 (f_equiv; intros ?).
    do 4 f_equiv.
    do 2 (f_equiv; intros ?).
    apply later_contractive.
    destruct m as [| m].
    - apply dist_later_0.
    - apply dist_later_S.
      f_equiv.
      + apply dist_later_S in H.
        solve_proper.
      + f_equiv.
        do 2 (f_equiv; intros ?).
        do 2 f_equiv.
        intros ?; simpl.
        f_equiv; intros ?.
        f_equiv.
        apply dist_later_S in H.
        solve_proper.
  Qed.

  Program Definition IT_Val_Rel := fixpoint IT_Val_Rel_pre.

  Lemma IT_Val_Rel_unfold : IT_Val_Rel ≡ IT_Val_Rel_pre IT_Val_Rel.
  Proof. apply fixpoint_unfold. Qed.

  Lemma IT_Val_Rel_unfold' v w : IT_Val_Rel v w ≡ IT_Val_Rel_pre IT_Val_Rel v w.
  Proof.
    do 2 f_equiv.
    apply IT_Val_Rel_unfold.
  Qed.

  Program Definition IT_Rel := IT_Rel_pre IT_Val_Rel.

  (* Global Instance IT_Val_Rel_persist e1 e2 : Persistent (IT_Val_Rel e1 e2). *)
  (* Proof. *)
  (*   rewrite IT_Val_Rel_unfold' /IT_Val_Rel_pre. *)
  (*   apply _. *)
  (* Qed. *)

  Lemma IT_Rel_ext_substL e1 e1' e2 : e1 ≡ e1' → IT_Rel e1 e2 ⊢ IT_Rel e1' e2.
  Proof.
    iIntros (H) "H".
    rewrite /IT_Rel /IT_Rel_pre /=.
    iIntros (j K) "G".
    rewrite -H.
    iApply "H"; iApply "G".
  Qed.

  Lemma IT_Rel_ext_substR e1 e2 e2' : e2 ≡ e2' → IT_Rel e1 e2 ⊢ IT_Rel e1 e2'.
  Proof.
    iIntros (H) "H".
    rewrite /IT_Rel /IT_Rel_pre /=.
    iIntros (j K) "G".
    iApply (wp_wand with "[H G]").
    - iApply ("H" $! j K).
      rewrite H.
      iApply "G".
    - iIntros (v) "J".
      by iModIntro.
  Qed.

  Lemma IT_Val_Rel_ext_substL e1 e1' e2 : e1 ≡ e1' → IT_Val_Rel e1 e2 ⊢ IT_Val_Rel e1' e2.
  Proof.
    iIntros (H) "H".
    iEval (rewrite IT_Val_Rel_unfold') in "H".
    iEval (rewrite IT_Val_Rel_unfold').
    rewrite /IT_Val_Rel_pre /=.
    iDestruct "H" as "[(%x & %y & H) | (%m & %f & %g & H1 & H2 & H3)]".
    - iLeft.
      iExists x, y.
      by rewrite -H.
    - iRight.
      iExists m, f, g.
      rewrite H.
      iSplit; first done.
      iSplit; first done.
      done.
  Qed.

  Lemma IT_Val_Rel_ext_substR e1 e2 e2' : e2 ≡ e2' → IT_Val_Rel e1 e2 ⊢ IT_Val_Rel e1 e2'.
  Proof.
    iIntros (H) "H".
    iEval (rewrite IT_Val_Rel_unfold') in "H".
    iEval (rewrite IT_Val_Rel_unfold').
    rewrite /IT_Val_Rel_pre /=.
    iDestruct "H" as "[(%x & %y & H) | (%m & %f & %g & H1 & H2 & H3)]".
    - iLeft.
      iExists x, y.
      by rewrite -H.
    - iRight.
      iExists m, f, g.
      rewrite H.
      iSplit; first done.
      iSplit; first done.
      done.
  Qed.

  Definition IT_Top_Rel e1 e2 : iProp :=
    spec_ctx → IT_Rel e1 e2.

  #[export] Instance elim_modal_bupd_logrel p e1 e2 P :
    ElimModal True p false (|==> P) P (IT_Rel e1 e2) (IT_Rel e1 e2).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (_) "(H1 & H2)".
    iIntros (j K) "H3".
    rewrite (bupd_fupd ⊤).
    iApply fupd_wp; first solve_proper.
    iMod "H1".
    iModIntro.
    iApply ("H2" with "H1 H3").
  Qed.

  (* Program Definition IT_ctx (f : IT -n> IT) : Prop := *)
  (*   ∃ Perr_rec : error → IT, *)
  (*   ∃ Pret_rec : R -n> IT, *)
  (*   ∃ Parr_rec : laterO (sumO IT IT -n> prodO IT IT) -n> IT, *)
  (*   ∃ Ptau_rec : laterO (prodO IT IT) -n> IT, *)
  (*   ∃ Pvis_rec : forall (op : opid F), *)
  (*     (oFunctor_car (Ins (F op)) (sumO IT IT) (prodO IT IT)) -n> *)
  (*       ((oFunctor_car (Outs (F op)) (prodO IT IT) (sumO IT IT)) -n> *)
  (*          laterO (prodO IT IT)) -n> *)
  (*       IT, *)
  (*   ∃ Punfold_rec : *)
  (*       IT -n> sumO (sumO (sumO (sumO R (laterO (IT -n> IT))) *)
  (*                            errorO) *)
  (*                      (laterO IT)) *)
  (*                (sigTO (λ op : opid F, *)
  (*                       prodO (oFunctor_apply (Ins (F op)) IT) *)
  (*                         ((oFunctor_apply (Outs (F op)) IT) -n> laterO IT))%type), *)
  (*   f = IT_rec1 IT *)
  (*                           Perr_rec *)
  (*                           Pret_rec *)
  (*                           Parr_rec *)
  (*                           Ptau_rec *)
  (*                           Pvis_rec *)
  (*                           Punfold_rec. *)

  (* Program Definition context_equiv (x y : IT) : iProp *)
  (*   := ∀ f σ, ⌜IT_ctx f⌝ *)
  (*             -∗ (∃ βv l σ' n, *)
  (*                   tp_internal_steps (Σ := Σ) (gReifiers_sReifier rs) [f x] σ *)
  (*                     ((IT_of_V βv) :: l) σ' n) *)
  (*             -∗ (∃ βv l σ' n, *)
  (*                   tp_internal_steps (gReifiers_sReifier rs) [f y] σ *)
  (*                     ((IT_of_V βv) :: l) σ' n). *)

  (* Lemma logrel_context_equiv (x y : IT) *)
  (*   : IT_Rel x y -∗ context_equiv x y. *)
  (* Proof. *)
  (*   iIntros "H". *)
  (*   iIntros (f σ) "%HCtx (%βv & %l & %σ' & %m & G)". *)
  (*   destruct HCtx as [f1 [f2 [f3 [f4 [f5 [f6 f7]]]]]]. *)
  (*   destruct (IT_dont_confuse x) *)
  (*     as [[e Ha2] | [[p Ha2] | [ [g Ha2] | [[la Ha2]|[op [i [k Ha2]]]] ]]]. *)
  (*   - rewrite f7. *)
  (*     assert (x = Err e) as ->; first admit. *)
  (*     iSpecialize ("H" $! 0). *)
  (*     admit. *)
  (*   - iDestruct (IT_Rel_ext_substL with "H") as "H"; first apply Ha2. *)
  (*     iSpecialize ("H" $! 0 HOM_id). *)
  (* Admitted. *)

  (* Lemma logrel_context_equiv' (x y : IT) f *)
  (*   : IT_Rel x y -∗ ⌜IT_ctx f⌝ -∗ IT_Rel (f x) (f y). *)
  (* Proof. *)
  (*   iIntros "H %HCtx". *)
  (*   iIntros (j K) "Hpt". *)
  (*   destruct (IT_dont_confuse x) *)
  (*     as [[e Ha2] | [[p Ha2] | [ [g Ha2] | [[la Ha2]|[op [i [k Ha2]]]] ]]]. *)
  (*   - admit. *)
  (*   -  *)
  (*     iDestruct (IT_Rel_ext_substL with "H") as "H"; first apply Ha2. *)
  (*     iSpecialize ("H" $! 0 HOM_id). *)

  (*     all: rewrite Ha2. *)
  (* Admitted. *)
End rel.

Notation "e1 ⪯ₑ e2 '@{' re \ A \ s '}'" := (IT_Rel re A s e1 e2) (at level 80).
Notation "e1 ⪯ᵥ e2 '@{' re \ A \ s '}'" := (IT_Val_Rel re A s e1 e2) (at level 80).
Notation "e1 ⪯ₚ e2 '@{' re \ A \ s '}'" := (IT_Top_Rel re A s e1 e2) (at level 80).

(* Lemma logrel_adequacy cr Σ `{!invGpreS Σ} n (rs : gReifiers NotCtxDep n) *)
(*   {A} `{!Cofe A} `{!statePreG rs A Σ} `{!inG Σ (tpoolUR rs A)} *)
(*   `{Inhabited (sReifier_state (gReifiers_sReifier rs) *)
(*                  ♯ IT (sReifier_ops (gReifiers_sReifier rs)) A)} *)
(*   (α β : IT _ A) σ βv σ' s l k (ψ : (ITV (gReifiers_ops rs) A) → Prop) : *)
(*   external_steps (gReifiers_sReifier rs) α σ (IT_of_V βv) σ' l k → *)
(*   (∀ `{H1 : !invGS Σ} `{H2 : !stateG rs A Σ} `{H3 : !tpoolSG rs A Σ}, *)
(*      (∀ βv, ⊢@{iProp Σ} ⌜ψ βv⌝) *)
(*      ∧ (£ cr ∗ has_full_state σ ⊢ (α) ⪯ₚ (β) @{ rs \ A \ s })%I) → *)
(*   ψ βv. *)
(* Proof. *)
(*   intros Hst Hprf. *)
(*   cut (⊢ ⌜ψ βv⌝ : iProp Σ)%I. *)
(*   { intros HH. eapply uPred.pure_soundness; eauto. } *)
(*   eapply (step_fupdN_soundness_lc _ 0 (1 + cr + 3*k)). *)
(*   intros Hinv. iIntros "[[Hcr' Hcr] Hlc]". *)
(*   iMod (new_state_interp rs σ) as (sg) "[Hs Hsfull]". *)
(*   iMod (new_state_interp rs σ) as (sg') "[Hs' Hsfull']". *)
(*   iMod (own_alloc ((to_tpool rs A []))) as (γ) "Ht". *)
(*   { by apply gmap_view_auth_dfrac_valid. } *)
(*   set (T := {| tpool_inG := _; tpool_name := γ |} : tpoolSG rs A Σ). *)
(*   iMod (tpool_alloc rs A β 0 [] with "[$Ht]") as "[Hpool Hth]"; first done. *)
(*   iMod (inv_alloc specN _ (spec_inv rs A [β] σ) with "[Hpool Hs']") as "#Hcfg". *)
(*   { *)
(*     iNext. iExists [β], σ, 0. *)
(*     iFrame "Hpool Hs'". *)
(*     by iApply tp_internal_steps_0. *)
(*   } *)
(*   destruct (Hprf Hinv sg T) as (Φ & Hprf'). *)
(*   iPoseProof (Hprf' with "[$Hcr $Hsfull] [Hcfg]") as "Hic". *)
(*   { iExists [β], σ. admit. } *)
(*   iSpecialize ("Hic" $! 0 HOM_id with "Hth"). *)
(*   iPoseProof (wp_internal_steps with "[]") as "Hphi". *)
(*   { *)
(*     iApply external_steps_internal_steps. *)
(*     apply Hst. *)
(*   } *)
(*   iMod ("Hphi" with "Hs Hic Hlc") as "[Hs [Hp Hts]]". *)
(*   iClear "Hphi". *)

(*   (* iMod (wp_val_inv with "Hp") as "[%βv' [Hp #Hval]]". *) *)
(*   (* { solve_proper. } *) *)
(*   (* iInv specN as (tp σ'' p) "[H1 [HS #H2]]" "HClose". *) *)
(*   (* iApply (lc_fupd_add_later with "Hcr'"). *) *)
(*   (* iNext. *) *)
(*   (* iDestruct (tpool_read with "H1 Hp") as "#HEQ". *) *)
(*   (* iMod ("HClose" with "[-Hs]") as "_". *) *)
(*   (* { iNext. iExists tp, σ'', p. iFrame "H1". iFrame "H2". iFrame "HS". } *) *)
(*   (* iPoseProof (Φ βv) as "HΦ". *) *)

(*   (* POI 2. we get internal steps, value relation. probably, we can also get something about state *) *)
(*   (* has_full_state in the spec *) *)
(*   (* epose proof (internal_step_safe_external_step (Σ := Σ) (gReifiers_sReifier rs) β σ). *) *)
(*   (* iApply fupd_mask_intro_discard; first done. *) *)
(* Abort. *)

Section basic_rules.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ} `{!tpoolSG rs R Σ} `{!stateG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Lemma IT_Rel_val v w
    : ⊢ (v) ⪯ᵥ (w) @{ rs \ R \ s }
        -∗ (IT_of_V v) ⪯ₑ (IT_of_V w) @{ rs \ R \ s }.
  Proof.
    iIntros "H" (j K) "G".
    iApply wp_val.
    iModIntro.
    iExists w.
    iFrame.
  Qed.

  Lemma IT_Rel_val' `{!IntoVal e1 v} `{!IntoVal e2 w}
    : ⊢ (v) ⪯ᵥ (w) @{ rs \ R \ s }
        -∗ (e1) ⪯ₑ (e2) @{ rs \ R \ s }.
  Proof.
    iIntros "H".
    iApply IT_Rel_ext_substL; first apply into_val.
    iApply IT_Rel_ext_substR; first apply into_val.
    by iApply IT_Rel_val.
  Qed.

  Lemma IT_Rel_Tick_l e1 e2
    : ⊢ ▷ ((e1) ⪯ₑ (e2) @{ rs \ R \ s })
        -∗ (Tick e1) ⪯ₑ (e2) @{ rs \ R \ s }.
  Proof.
    iIntros "H" (j K) "G".
    iApply wp_tick.
    iNext.
    by iApply "H".
  Qed.

  Lemma IT_Rel_bottom e
    : ⊢ (core.Bottom) ⪯ₑ (e) @{ rs \ R \ s }.
  Proof.
    iLöb as "IH".
    iApply IT_Rel_ext_substL.
    - symmetry; apply Bottom_unfold.
    - iApply IT_Rel_ext_substL.
      + apply Tick_eq.
      + by iApply IT_Rel_Tick_l.
  Qed.

  (* Lemma IT_Rel_Eff *)
  (*   `{subR : !subReifier sR rs} *)
  (*   (op : opid (sReifier_ops sR)) *)
  (*   (x : Ins (sReifier_ops sR op) ♯ IT) *)
  (*   (y : Outs (sReifier_ops sR op) ♯ IT) *)
  (*   (k : Outs (F (subEff_opid op)) ♯ IT -n> laterO IT) *)
  (*   (σ σ' : sReifier_state sR ♯ IT) β l e : *)
  (*   sReifier_re sR op (x, σ) ≡ Some (y, σ', l) → *)
  (*   k (subEff_outs y) ≡ Next β → *)
  (*   has_substate σ *)
  (*   -∗ ▷ (£ 1 -∗ has_substate σ' *)
  (*         -∗ ([∗ list] ef ∈ listO_map Tau l, WP@{rs} ef @ s {{ _, True }}) *)
  (*         ∗ (β) ⪯ₑ (e) @{ rs \ R \ s}) *)
  (*   -∗ (Vis (subEff_opid op) (subEff_ins x) k) ⪯ₑ (e) @{ rs \ R \ s}. *)
  (* Proof. *)
  (*   iIntros (H1 H2) "Hσ G". *)
  (*   iIntros (j K) "J". *)
  (*   iPoseProof (wp_subreify_ctx_indep with "[Hσ]") as "J'". *)
  (*   iApply (wp_subreify_ctx_indep with "Hσ"); [eassumption | eassumption |]. *)
  (*   iNext. *)
  (*   iIntros "Hlc Hσ". *)
  (*   iDestruct ("G" with "Hlc Hσ") as "(G1 & G2)". *)
  (*   iFrame "G1". *)
  (*   by iApply "G2". *)
  (* Qed. *)
End basic_rules.

Require Import gitrees.gitree.subofe.
Require Import gitrees.gitree.lambda.
Require Import gitrees.effects.store.
Require Import gitrees.lib.factorial.

Section example.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context `{!subReifier reify_store rs}.
  Context `{!subReifier reify_io rs}.
  Context (R : ofe) `{!Cofe R}.
  Context `{!SubOfe natO R, !SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ} `{!tpoolSG rs R Σ} `{!stateG rs R Σ} `{!heapG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Context (s : stuckness).
  Notation HOM := (@HOM R _ F).

  Example prog3 : ITV := FunV (Next (λne x, x)).
  Program Example prog4 : IT := λit x, LET (Ret 5) (constO x).
  Next Obligation.
    intros ??? H.
    by do 2 f_equiv.
  Qed.

  Example prog3_prog4_rel :  ⊢ (IT_of_V prog3) ⪯ₚ (prog4) @{ rs \ R \ s }.
  Proof.
    iIntros "#HInv".
    iApply IT_Rel_val'.
    rewrite IT_Val_Rel_unfold'.
    iRight.
    iExists 1, _, _. iSplit; first done. iSplit; first done.
    iSplit; first admit.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "H HCred" (j K).
    iIntros "Hpt".
    iApply wp_val.
    iModIntro.
    iExists w.
    iFrame "H".
    rewrite /= LET_Val /=.
    done.
  Admitted.

  Program Example prog5 : IT := λit x, ALLOC (Ret 5) (constO x).
  Next Obligation.
    intros ??? H.
    by do 2 f_equiv.
  Qed.

  Example prog5_prog3_rel : heap_ctx rs
                            -∗ (prog5) ⪯ₚ (IT_of_V prog3) @{ rs \ R \ s }.
  Proof.
    iIntros "#HHeap #HInv".
    iApply IT_Rel_val'.
    rewrite IT_Val_Rel_unfold'.
    iRight.
    iExists 1, _, _. iSplit; first done. iSplit; first done.
    iSplit; first admit.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "H HCred" (j K).
    iIntros "Hpt".
    iSimpl.
    iApply (wp_alloc with "HHeap [HCred Hpt H]"); first solve_proper.
    do 2 iNext.
    iIntros (l) "Hpt'".
    iSimpl.
    iApply wp_val.
    iModIntro.
    iExists w.
    iFrame "Hpt".
    done.
  Admitted.

    Example prog5_prog5_rel `{!Inhabited (gReifiers_state rs ♯ IT)}
    : heap_ctx rs
      -∗ (prog5) ⪯ₚ (prog5) @{ rs \ R \ s }.
  Proof.
    iIntros "#HHeap #HInv".
    iApply IT_Rel_val'.
    rewrite IT_Val_Rel_unfold'.
    iRight.
    iExists 1, _, _. iSplit; first done. iSplit; first done.
    iSplit; first admit.
    iModIntro.
    iIntros (v w).
    iNext.

    (* IT_Rel should have elim modal *)
    iIntros "H HCred" (j K).

    iIntros "HPt".
    simpl.

    (* iDestruct "HInv" as (σ l) "HInv". *)
    iApply (wp_alloc with "HHeap"); first solve_proper.
    (* iPoseProof (step_reify_hom rs R K ⊤ j) as "G". *)

    (* iApply fupd_wp; first solve_proper. *)
    (* iInv specN as (tp σ'' p) "[H1 [HS #H2]]" "HClose".     *)
    (* iApply (wp_alloc with "HHeap"); first solve_proper. *)
    (* iDestruct (bi.later_intro with "HPt") as "HPt".     *)
    (* iApply fupd_mask_intro. *)

    do 2 iNext.
    iIntros (l') "HPt'".
    iApply wp_val.
    iModIntro.
    iExists w.
    iFrame "H".
    (* XXX: same stuff with credits *)
    (* probably put them into it rel val (function case) *)
  Abort.


  (* POI 3. no rules for effects at the right-hand side *)
  Example prog3_prog5_rel `{!Inhabited (gReifiers_state rs ♯ IT)}
    : heap_ctx rs
      -∗ (IT_of_V prog3) ⪯ₚ (prog5) @{ rs \ R \ s }.
  Proof.
    iIntros "#HHeap #HInv".
    iApply IT_Rel_val'.
    rewrite IT_Val_Rel_unfold'.
    iRight.
    iExists 1, _, _. iSplit; first done. iSplit; first done.
    iSplit; first admit.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "H HCred" (j K).
    iIntros "Hpt".
    iSimpl in "Hpt".
    iApply wp_val.

    iInv (nroot.@"storeE") as (σ') "(>J1 & J2 & J3)" "HClose'".
    iMod (step_reify_hom rs R K (⊤ ∖ ↑nroot.@"storeE") j _ _ _ _ σ'
           with "[$J1 $J2 Hpt $HInv]") as "(Hpt & _ & Hs)".
    {
      assert (nroot.@"spec" ## nroot.@"storeE").
      { apply ndot_ne_disjoint. done. }
      set_solver.
    }
    {
      iSplitR "Hpt"; last first.
      - iSplit; last first.
        + iNext.
          iApply "Hpt".
        + by simpl.
      - by simpl.
    }
    iExists w.
    iFrame "Hpt H".
    iApply "HClose'".
    iNext.

    (* XXX: auth shouldn't be in spec_inv. it's step rule task to handle it *)
    iExists _; iFrame "Hs".
  Abort.

  Program Example prog6 : IT := (IT_of_V prog3) ⊙ (IT_of_V prog3).

  Example prog3_prog6_rel `{!Inhabited (gReifiers_state rs ♯ IT)}
    : £ 1 -∗ (IT_of_V prog3) ⪯ₚ (prog6) @{ rs \ R \ s }.
  Proof.
    iIntros "HCred #HInv".
    iIntros (j K) "Hpt".
    iApply wp_val.
    iExists prog3.
    rewrite /prog6.
    rewrite APP'_Fun_l laterO_map_Next /= -Tick_eq hom_tick.
    iMod (step_tick rs R ⊤ j with "[$HCred $HInv $Hpt]") as "Hwk";
      first set_solver.
    iModIntro.
    iFrame "Hwk".
    rewrite IT_Val_Rel_unfold'.
    iRight.
    iExists 1, _, _. iSplit; first done. iSplit; first done.
    iSplit; first admit.
    iModIntro.
    iIntros (v w).
    iNext.
    iIntros "H HCred" (j' K').
    iIntros "Hpt".
    iApply wp_val.
    iModIntro.
    iExists w.
    iFrame "H Hpt".
  Admitted.

  (* TODO *)
  (* Example prog1 : IT := fact_imp n rs. *)

  (* Example prog2 (self : laterO IT) : IT := λit x, *)
  (*     IF x *)
  (*       (NATOP (Nat.mul) x (APP' self (NATOP Nat.sub x (Ret 1)))) *)
  (*       1. *)

  (* Example prog1_prog2_rel : ⊢ (prog1) ⪯ₑ (prog2) @{ rs \ R \ s }. *)
End example.

(* (** * The induction principle *) *)
(* Section IT_ind. *)
(*   Context {E : opsInterp}. *)
(*   Context {A : ofe} `{!Cofe A}. *)
(*   Context {Σ : gFunctor}. *)
(*   Context {PROP : bi} `{!BiLöb PROP} `{!BiAffine PROP}. *)
(*   Variable (P : IT E A -n> PROP). *)
(*   Variable (Q : ∀ i, Ins (opsInterp_lookup E i) ♯ IT E A -n> PROP). *)
(*   Variable (R : ∀ i, Outs (opsInterp_lookup E i) ♯ IT E A -n> PROP).  *)

(*   Lemma P_ind (Perr : ⊢ ∀ e, P (Err e)) *)
(*     (Pret : ⊢ ∀ a, P (Ret a)) *)
(*     (Parr : ⊢ ∀ f : IT E A -n> IT E A, *)
(*        ▷ (∀ a, P a -∗ P (f a)) -∗ P (Fun (Next f))) *)
(*     (Ptau : ⊢ ∀ a, ▷ (P a) -∗ P (Tick a)) *)
(*     (Pvis : ⊢ ∀ i x (k : _ -n> _), *)
(*        Q i x -∗ ▷ (∀ y, R i y -∗ P (Tau (k y))) -∗ P (Vis i x k)) *)
(*     : ⊢ ∀ x, P x. *)
(*   Proof. *)
(*     iLöb as "IH". *)
(*     iIntros (y). *)
(*     destruct (IT_dont_confuse y) *)
(*       as [[e Ha2] | [[m Ha2] | [ [g Ha2] | [[la Ha2]|[op [i [k Ha2]]]] ]]]. *)
(*     all: rewrite Ha2. *)
(*     - iApply Perr. *)
(*     - iApply Pret. *)
(*     - destruct (Next_uninj g) as [x ->]. *)
(*       iApply Parr. *)
(*       iNext. *)
(*       iIntros (a) "G". *)
(*       iApply "IH". *)
(*     - iApply Ptau. *)
(*       iNext. *)
(*       iApply "IH". *)
(*     - iApply Pvis. *)
(*       + admit. *)
(*       + iNext. *)
(*         iIntros (a) "H". *)
(*         iApply "IH". *)
(*   Admitted. *)
(* End IT_ind. *)

Section rules.
  Context {n : nat} (rs : gReifiers NotCtxDep n).
  Notation F := (gReifiers_ops rs).
  Context (R : ofe) `{!Cofe R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ} `{!tpoolSG rs R Σ} `{!stateG rs R Σ}.
  Notation iProp := (iProp Σ).
  Notation coPsetO := (leibnizO coPset).
  Definition s : stuckness := λ _, True.
  Notation HOM := (@HOM R _ F).

  (* Lemma IT_Rel_refl e *)
  (*   : ⊢ (e) ⪯ₑ (e) @{ rs \ R \ s }. *)
  (* Proof. *)
  (*   iStartProof. *)
  (*   iRevert (e). *)
  (*   iLöb as "IH". *)
  (*   iIntros (e). *)
  (*   destruct (IT_dont_confuse e) *)
  (*     as [[t Ha2] | [[m Ha2] | [ [g Ha2] | [[la Ha2]|[op [i [k Ha2]]]] ]]].       *)
  (*   - iIntros (j K) "HH". *)
  (*     rewrite Ha2. *)
  (*     by iApply wp_err. *)
  (*   - iIntros (j K) "HH". *)
  (*     rewrite Ha2. *)
  (*     iApply wp_val. *)
  (*     iModIntro. *)
  (*     iExists (RetV m). *)
  (*     iFrame "HH". *)
  (*     rewrite IT_Val_Rel_unfold'.       *)
  (*     iLeft. *)
  (*     by iExists m, m. *)
  (*   - iIntros (j K) "HH". *)
  (*     rewrite Ha2. *)
  (*     iApply wp_val. *)
  (*     iModIntro. *)
  (*     iExists (FunV g). *)
  (*     iFrame "HH". *)
  (*     rewrite IT_Val_Rel_unfold'.       *)
  (*     iRight. *)
  (*     destruct (Next_uninj g) as [g' HEQ]. *)
  (*     iExists g', g'. *)
  (*     iSplit; first done. *)
  (*     iSplit; first done. *)
  (*     iModIntro. *)
  (*     iIntros (v w). *)
  (*     iNext. *)
  (*     iIntros "H". *)
  (*     iIntros (j' K') "HH". *)
  (*     iApply ("IH" $! (g' (IT_of_V v)) j' K').       *)
  (*     (* tpool_pointsto should be related *)       *)
  (*     admit. *)
  (*   - iIntros (j K) "HH". *)
  (*     rewrite Ha2. *)
  (*     iApply wp_tick. *)
  (*     iNext. *)
  (*     iSpecialize ("IH" $! la j K). *)
  (*     (* fixable *) *)
  (*     iAssert (tpool_pointsto rs R j (K la)) with "[HH]" as "HH". *)
  (*     { admit. } *)
  (*     iSpecialize ("IH" with "HH"). *)
  (*     iApply "IH". *)
  (*   - iApply IT_Rel_ext_substL. *)
  (*     { symmetry. apply Ha2. } *)
  (*     iIntros (j K) "HH". *)
  (*     rewrite Ha2. *)
  (* Admitted. *)

  (*   unshelve iApply (P_ind (λne x, (x) ⪯ₑ (x) @{ rs \ R \ s})). *)
  (*   - solve_proper. *)
  (*   - intros i. apply (λne x, True)%I. *)
  (*   - intros i. apply (λne x, True)%I. *)
  (*   - iIntros (e'). *)
  (*     iIntros (j K) "HH". *)
  (*     iApply wp_err. *)
  (*     (* depends on stuckness *) *)
  (*     (* reflexive on errors *) *)
  (*     admit. *)
  (*   - iIntros (a j K) "HH". *)
  (*     iApply wp_val. *)
  (*     iModIntro. *)
  (*     iExists (RetV a). *)
  (*     iFrame "HH". *)
  (*     rewrite IT_Val_Rel_unfold'.       *)
  (*     iLeft. *)
  (*     by iExists a, a. *)
  (*   - iIntros (f) "GG". *)
  (*     iIntros (j K) "HH". *)
  (*     iApply wp_val. *)
  (*     iModIntro. *)
  (*     iExists (FunV (Next f)). *)
  (*     iFrame "HH". *)
  (*     rewrite IT_Val_Rel_unfold'.       *)
  (*     iRight. *)
  (*     iExists f, f. *)
  (*     iSplit; first done. *)
  (*     iSplit; first done. *)
  (*     iIntros (v w). *)
  (*     admit. *)
  (*     (* can't be persistent *) *)
  (*   - iIntros (a) "GG". *)
  (*     iIntros (j K) "HH". *)
  (*     iApply wp_tick. *)
  (*     iNext. *)
  (*     iApply "GG". *)
  (*     admit. *)
  (*     (* correct, but requires some prelim work *) *)
  (* Qed. *)

  (* iIntros (j K) "H". *)
  (*   iApply wp_bind. *)

  (*   iApply (wp_wand). *)
  (*   - iApply (wp_bind).            *)

  (* Lemma IT_Val_Rel_refl v *)
  (*   : ⊢ (v) ⪯ᵥ (v) @{ rs \ R \ s }. *)
  (* Proof. *)
  (*   destruct v as [b | f]. *)
  (*   - rewrite IT_Val_Rel_unfold'. *)
  (*     iLeft. *)
  (*     iExists b, b. *)
  (*     done. *)
  (*   - rewrite IT_Val_Rel_unfold'. *)
  (*     iRight. *)
  (*     destruct (Next_uninj f) as [g H]. *)
  (*     iExists g, g. *)
  (*     iSplit; first (by rewrite H). *)
  (*     iSplit; first (by rewrite H). *)
  (*     iModIntro. *)
  (*     iIntros (v w). *)
  (*     iNext. *)
  (*     iIntros "H". *)
  (*     iIntros (K1 K2) "#G". *)

  (*   iIntros (v1 v2). *)
  (*   iModIntro. *)
  (*   iIntros "H". *)
  (*   iApply wp_val. *)
  (*   iModIntro. *)
  (*   iApply wp_val. *)
  (*   done. *)
  (* Qed. *)

  (* Lemma IT_Frame_Rel_compose W1 W2 K1 K2 *)
  (*   : ⊢ (W1) ⪯ₖ (W2) @{ rs \ R \ s } *)
  (*       -∗ (K1) ⪯ₖ (K2) @{ rs \ R \ s } *)
  (*       -∗ (HOM_compose K1 W1) ⪯ₖ (HOM_compose K2 W2) @{ rs \ R \ s }. *)
  (* Proof. *)
  (*   iIntros "#H #G". *)
  (*   iModIntro. *)
  (*   iIntros (v1 v2) "#J". *)
  (*   iEval (simpl). *)
  (*   iApply wp_bind. *)
  (*   iApply (wp_wand with "[H J]"). *)
  (*   - iApply "H"; iApply "J". *)
  (*   - iIntros (v) "K". *)
  (*     iModIntro.       *)
  (*     iApply (wp_wand with "[G H]"). *)
  (*     + iApply "G". *)
  (*       iApply  *)
  (*       admit. *)
  (*     +  *)
  (*   simpl. *)


  (* Lemma IT_Rel_HOM (K : HOM) e1 e2 *)
  (*   : ⊢ (e1) ⪯ₑ (e2) @{ rs \ R \ s } *)
  (*       -∗ (K e1) ⪯ₑ (K e2) @{ rs \ R \ s }. *)
  (* Proof. *)
  (*   iIntros "H" (j K') "G".     *)
  (*   iApply wp_bind; first solve_proper. *)
  (*   iSpecialize ("H" $! j (HOM_compose K' K) with "G"). *)
  (*   iApply (wp_wand with "H"). *)
  (*   iIntros (v) "(%v' & H1 & H2)". *)
  (*   iLöb as "IH". *)
  (*   iModIntro. *)
  (*   iApply wp_bind; first solve_proper. *)
  (*   iApply wp_val. *)
  (*   iModIntro. *)


  (* Lemma IT_Rel_app f g v w *)
  (*   : ⊢ (v) ⪯ᵥ (w) @{ rs \ R \ s } *)
  (*       -∗ (FunV (Next f)) ⪯ᵥ (FunV (Next g)) @{ rs \ R \ s } *)
  (*       -∗ (f (IT_of_V v)) ⪯ₑ (g (IT_of_V w)) @{ rs \ R \ s }. *)
  (* Proof. *)
  (*   iIntros "H G" (K1 K2) "J". *)
  (*   iEval (rewrite IT_Val_Rel_unfold') in "G". *)
  (*   iDestruct "G" as "[G1 | G2]". *)
  (*   - iExFalso. *)
  (*     iDestruct "G1" as "(%x & %y & G1 & G2)". *)
  (*     iApply (IT_ret_fun_ne x (Next f)). *)
  (*     iApply internal_eq_sym. *)
  (*     iApply (f_equivI IT_of_V with "G1"). *)
  (*   - iDestruct "G2" as "(%x & %y & G1 & G2 & G3)". *)

End rules.
