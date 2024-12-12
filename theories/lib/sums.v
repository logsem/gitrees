(** Encoding of sums *)
From gitrees Require Import prelude gitree hom.
From gitrees.gitree Require Import core lambda.

Section sums.
  Context {Σ : opsInterp} {A : ofe} `{!Cofe A}.

  Notation IT := (IT Σ A).
  Notation ITV := (ITV Σ A).

  Program Definition injl_ITf : IT -n> IT := λne a, λit l _, l ⊙ a.
  Solve All Obligations with solve_proper_please.
  Global Instance injl_ITf_AsVal α : AsVal (injl_ITf α).
  Proof. eexists (FunV _); simpl; reflexivity. Qed.
  Program Definition injl_IT : IT := λit a, injl_ITf a.
  Solve All Obligations with solve_proper_please.
  Program Definition injl_ITV : IT -n> IT := λne t, injl_IT ⊙ t.
  Lemma injl_ITV_apply α `{!AsVal α} : injl_ITV α ≡ Tick (injl_ITf α).
  Proof. by rewrite /injl_ITf /= APP'_Fun_l laterO_map_Next -Tick_eq. Qed.
  Lemma injl_ITV_tick α : injl_ITV (Tick α) ≡ Tick $ injl_ITV α.
  Proof. by rewrite /injl_ITf /= APP'_Tick_r. Qed.
  Lemma injl_ITV_tick_n α n : injl_ITV (Tick_n n α) ≡ Tick_n n $ injl_ITV α.
  Proof.
    induction n as [| n IHn]; first by reflexivity.
    by rewrite injl_ITV_tick IHn.
  Qed.
  Lemma injl_ITV_err e : injl_ITV (Err e) ≡ Err e.
  Proof. by rewrite /= APP'_Err_r. Qed.
  Lemma injl_ITV_vis op i k : injl_ITV (Vis op i k)
                                ≡ Vis op i (laterO_map (injl_ITV) ◎ k).
  Proof.
    rewrite /= APP'_Vis_r.
    do 3 f_equiv.
    intro; simpl.
    reflexivity.
  Qed.
  Global Instance injl_ITV_hom : IT_hom injl_ITV.
  Proof.
    eapply IT_HOM.
    - apply injl_ITV_tick.
    - apply injl_ITV_vis.
    - apply injl_ITV_err.
  Qed.
  Definition injl_ITV_HOM : HOM := MkHom injl_ITV _.

  Program Definition injr_ITf : IT -n> IT := λne a, λit _ r, r ⊙ a.
  Solve All Obligations with solve_proper_please.
  Global Instance injr_ITf_AsVal α : AsVal (injr_ITf α).
  Proof. eexists (FunV _); simpl; reflexivity. Qed.
  Program Definition injr_IT : IT := λit a, injr_ITf a.
  Solve All Obligations with solve_proper_please.
  Program Definition injr_ITV : IT -n> IT := λne t, injr_IT ⊙ t.
  Lemma injr_ITV_apply α `{!AsVal α} : injr_ITV α ≡ Tick (injr_ITf α).
  Proof. by rewrite /injr_ITf /= APP'_Fun_l laterO_map_Next -Tick_eq. Qed.
  Lemma injr_ITV_tick α : injr_ITV (Tick α) ≡ Tick $ injr_ITV α.
  Proof. by rewrite /injr_ITf /= APP'_Tick_r. Qed.
  Lemma injr_ITV_tick_n α n : injr_ITV (Tick_n n α) ≡ Tick_n n $ injr_ITV α.
  Proof.
    induction n as [| n IHn]; first by reflexivity.
    by rewrite injr_ITV_tick IHn.
  Qed.
  Lemma injr_ITV_err e : injr_ITV (Err e) ≡ Err e.
  Proof. by rewrite /= APP'_Err_r. Qed.
  Lemma injr_ITV_vis op i k : injr_ITV (Vis op i k)
                                ≡ Vis op i (laterO_map (injr_ITV) ◎ k).
  Proof.
    rewrite /= APP'_Vis_r.
    do 3 f_equiv.
    intro; simpl.
    reflexivity.
  Qed.
  Global Instance injr_ITV_hom : IT_hom injr_ITV.
  Proof.
    eapply IT_HOM.
    - apply injr_ITV_tick.
    - apply injr_ITV_vis.
    - apply injr_ITV_err.
  Qed.
  Definition injr_ITV_HOM : HOM := MkHom injr_ITV _.

  Program Definition bimap_ITf : IT := λit s f g, s ⊙ f ⊙ g.
  Solve All Obligations with solve_proper_please.
  Program Definition bimap_ITV : IT -> IT -> IT -> IT
    := λ s f g, bimap_ITf ⊙ s ⊙ f ⊙ g.
  Global Instance bimap_ITV_Proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) bimap_ITV.
  Proof. repeat intros ?. rewrite /bimap_ITV /bimap_ITf /=; solve_proper_please. Qed.
  Global Instance bimap_ITV_ne n
    : Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) bimap_ITV.
  Proof. repeat intros ?. rewrite /bimap_ITV /bimap_ITf /=; solve_proper_please. Qed.

  Program Definition bimap_IT : IT -n> IT -n> IT -n> IT
    := λne s a b, get_val (λne v2, get_val (λne v1, bimap_ITV s v1 v2) a) b.
  Solve All Obligations with solve_proper_please.

  Lemma bimap_inl_IT α f g `{!AsVal α, !AsVal f, !AsVal g}
    : bimap_ITV (injl_ITV α) f g ≡ Tick_n 6 (f ⊙ α).
  Proof.
    rewrite injl_ITV_apply.
    rewrite /bimap_ITV.
    rewrite /bimap_ITf /=.
    rewrite APP'_Tick_r APP'_Tick_l APP'_Fun_l laterO_map_Next /=.
    do 3 rewrite APP'_Tick_l.
    rewrite APP'_Fun_l laterO_map_Next /=.
    rewrite APP'_Tick_l.
    rewrite APP'_Fun_l laterO_map_Next /=.
    rewrite APP'_Fun_l laterO_map_Next /=.
    rewrite APP'_Tick_l.
    rewrite APP'_Fun_l laterO_map_Next /=.
    reflexivity.
  Qed.

  Lemma bimap_inr_IT α f g `{!AsVal α, !AsVal f, !AsVal g}
    : bimap_ITV (injr_ITV α) f g ≡ Tick_n 6 (g ⊙ α).
  Proof.
    rewrite injr_ITV_apply.
    rewrite /bimap_ITV.
    rewrite /bimap_ITf /=.
    rewrite APP'_Tick_r APP'_Tick_l APP'_Fun_l laterO_map_Next /=.
    do 3 rewrite APP'_Tick_l.
    rewrite APP'_Fun_l laterO_map_Next /=.
    rewrite APP'_Tick_l.
    rewrite APP'_Fun_l laterO_map_Next /=.
    rewrite APP'_Fun_l laterO_map_Next /=.
    rewrite APP'_Tick_l.
    rewrite APP'_Fun_l laterO_map_Next /=.
    reflexivity.
  Qed.
End sums.
