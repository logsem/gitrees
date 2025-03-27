From gitrees Require Import prelude gitree utils.finite_sets.
Require Import List.
Import ListNotations.

Require Import Binding.Lib Binding.Set.

Section ctx_interp.
  Local Open Scope type.
  Context {E: opsInterp}.
  Context {R} `{!Cofe R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Definition interp_scope (S : Set) : ofe := (leibnizO S) -n> IT.

  Global Instance interp_scope_cofe S : Cofe (interp_scope S).
  Proof. apply _. Qed.

  Global Instance interp_scope_inhab S : Inhabited (interp_scope S).
  Proof. apply _. Defined.

  Program Definition interp_var {S : Set} (v : S) : interp_scope S -n> IT :=
    λne (f : interp_scope S), f v.
  Next Obligation.
    solve_proper.
  Qed.

  Program Definition ı_scope : interp_scope Empty_set
    := λne (x : ∅), match x with end.

  Definition interp_scope_split {S1 S2 : Set} :
    interp_scope (sum S1 S2) -n> interp_scope S1 * interp_scope S2.
  Proof.
    simple refine (λne (f : interp_scope (sum S1 S2)), _).
    - split.
      + simple refine (λne x, _).
        apply (f (inl x)).
      + simple refine (λne x, _).
        apply (f (inr x)).
    - repeat intro; simpl.
      repeat f_equiv; intro; simpl; f_equiv; assumption.
  Defined.

  Global Instance interp_var_proper {S : Set} (v : S) : Proper ((≡) ==> (≡)) (interp_var v).
  Proof. apply ne_proper. apply _. Qed.

  Program Definition extend_scope {S : Set}  : interp_scope S -n> IT -n> interp_scope (inc S)
    := λne γ μ x, let x' : inc S := x in
                  match x' with
                  | VZ => μ
                  | VS x'' => γ x''
                  end.
  Next Obligation.
    intros ???? [| x] [| y]; term_simpl; [solve_proper | inversion 1 | inversion 1 | inversion 1; by subst].
  Qed.
  Next Obligation.
    intros ??????.
    intros [| a]; term_simpl; solve_proper.
  Qed.
  Next Obligation.
    intros ??????.
    intros [| a]; term_simpl; solve_proper.
  Qed.

  Program Definition ren_scope {S S'} (δ : S [→] S') (env : interp_scope S')
    : interp_scope S := λne x, env (δ x).

End ctx_interp.

(* (* Common definitions and lemmas for Kripke logical relations *) *)
(* Section kripke_logrel. *)
(*   Variable s : stuckness. *)

(*   Context {sz : nat} {a : is_ctx_dep}. *)
(*   Variable rs : gReifiers a sz. *)
(*   Context {R} `{!Cofe R}. *)

(*   Notation F := (gReifiers_ops rs). *)
(*   Notation IT := (IT F R). *)
(*   Notation ITV := (ITV F R). *)
(*   Context `{!invGS Σ, !stateG rs R Σ}. *)
(*   Notation iProp := (iProp Σ). *)

(*   Context {A:ofe}. (* The type & predicate for the explicit Kripke worlds *) *)
(*   Variable (P : A -n> iProp). *)

(*   Implicit Types α β : IT. *)
(*   Implicit Types αv βv : ITV. *)
(*   Implicit Types Φ Ψ : ITV -n> iProp. *)

(*   Program Definition expr_pred (α : IT) (Φ : ITV -n> iProp) : iProp := *)
(*     (∀ x : A, P x -∗ wp rs α s ⊤ (λne v, ∃ y : A, Φ v ∗ P y)). *)
(*   Next Obligation. *)
(*     solve_proper. *)
(*   Qed. *)

(*   Global Instance expr_pred_ne {n} : Proper (dist n ==> dist n ==> dist n) expr_pred. *)
(*   Proof. *)
(*     intros ??????. *)
(*     unfold expr_pred. *)
(*     simpl. *)
(*     f_equiv. *)
(*     intros ?; simpl. *)
(*     f_equiv. *)
(*     f_equiv; first done. *)
(*     intros ?; simpl. *)
(*     f_equiv. *)
(*     intros ?; simpl. *)
(*     solve_proper. *)
(*   Qed. *)

(*   Global Instance expr_pred_proper : Proper (equiv ==> equiv ==> equiv) expr_pred. *)
(*   Proof. *)
(*     intros ??????. *)
(*     unfold expr_pred. *)
(*     simpl. *)
(*     f_equiv. *)
(*     intros ?; simpl. *)
(*     f_equiv. *)
(*     f_equiv; first done. *)
(*     intros ?; simpl. *)
(*     f_equiv. *)
(*     intros ?; simpl. *)
(*     solve_proper. *)
(*   Qed. *)

(*   Lemma expr_pred_ret α αv Φ `{!IntoVal α αv} : *)
(*     Φ αv ⊢ expr_pred α Φ. *)
(*   Proof. *)
(*     iIntros "H". *)
(*     iIntros (x) "Hx". iApply wp_val. *)
(*     simpl. *)
(*     iExists x. *)
(*     by iFrame. *)
(*   Qed. *)

(*   Lemma expr_pred_frame α Φ : *)
(*     WP@{rs} α @ s {{ Φ }} ⊢ expr_pred α Φ. *)
(*   Proof. *)
(*     iIntros "H". *)
(*     iIntros (x) "Hx". *)
(*     iApply (wp_wand with "H"). *)
(*     simpl. *)
(*     iIntros (v) "Hv". *)
(*     iExists x. *)
(*     by iFrame. *)
(*   Qed. *)

(* End kripke_logrel. *)

(* Section kripke_logrel_ctx_indep. *)
(*   Variable s : stuckness. *)

(*   Context {sz : nat}. *)
(*   Variable rs : gReifiers NotCtxDep sz. *)
(*   Context {R} `{!Cofe R}. *)

(*   Notation F := (gReifiers_ops rs). *)
(*   Notation IT := (IT F R). *)
(*   Notation ITV := (ITV F R). *)
(*   Context `{!invGS Σ, !stateG rs R Σ}. *)
(*   Notation iProp := (iProp Σ). *)

(*   Context {A : ofe}. *)
(*   Variable (P : A -n> iProp). *)

(*   Implicit Types α β : IT. *)
(*   Implicit Types αv βv : ITV. *)
(*   Implicit Types Φ Ψ : ITV -n> iProp. *)

(*   Local Notation expr_pred := (expr_pred s rs P). *)

(*   Lemma expr_pred_bind f `{!IT_hom f} α Φ Ψ `{!NonExpansive Φ} *)
(*     : expr_pred α Ψ ⊢ *)
(*       (∀ αv, Ψ αv -∗ expr_pred (f (IT_of_V αv)) Φ) *)
(*       -∗ expr_pred (f α) Φ. *)
(*   Proof. *)
(*     iIntros "H1 H2". *)
(*     iIntros (x) "Hx". *)
(*     iApply wp_bind. *)
(*     iSpecialize ("H1" with "Hx"). *)
(*     iApply (wp_wand with "H1"). *)
(*     iIntros (βv). iDestruct 1 as (y) "[Hb Hy]". *)
(*     iModIntro. *)
(*     iApply ("H2" with "Hb Hy"). *)
(*   Qed. *)
(* End kripke_logrel_ctx_indep. *)

(* Arguments expr_pred_bind {_ _ _ _ _ _ _ _ _ _} f {_ _}. *)

(* Section tm_interp. *)
(*   Context {sz : nat} {a : is_ctx_dep}. *)
(*   Variable rs : gReifiers a sz. *)
(*   Context {R} `{!Cofe R}. *)

(*   Notation F := (gReifiers_ops rs). *)
(*   Notation IT := (IT F R). *)
(*   Notation ITV := (ITV F R). *)
(*   Context `{!invGS Σ, !stateG rs R Σ}. *)
(*   Notation iProp := (iProp Σ). *)

(*   Context {A : ofe}. *)
(*   Variable (P : A -n> iProp). *)

(*   Variable (ty : Set). *)
(*   Variable (interp_ty : ty → (ITV -n> iProp)). *)
(*   Variable (kripke : IT → (ITV -n> iProp) → iProp). *)

(*   Definition ssubst_valid1 {S : Set} *)
(*     (Γ : S -> ty) *)
(*     (ss : interp_scope S) : iProp := *)
(*     (∀ x, □ kripke (ss x) (interp_ty (Γ x)))%I. *)

(*   Global Instance ssubst_valid_pers `{∀ τ β, Persistent (interp_ty τ β)} *)
(*     {S : Set} (Γ : S → ty) ss : Persistent (ssubst_valid1 Γ ss). *)
(*   Proof. apply _. Qed. *)

(* End tm_interp. *)

(* Section tm_interp_fin. *)
(*   Context {sz : nat} {a : is_ctx_dep}. *)
(*   Variable rs : gReifiers a sz. *)
(*   Context {R} `{!Cofe R}. *)

(*   Notation F := (gReifiers_ops rs). *)
(*   Notation IT := (IT F R). *)
(*   Notation ITV := (ITV F R). *)
(*   Context `{!invGS Σ, !stateG rs R Σ}. *)
(*   Notation iProp := (iProp Σ). *)

(*   Context {A : ofe}. *)
(*   Variable (P : A -n> iProp). *)

(*   Variable (ty : Set). *)
(*   Variable (interp_ty : ty → (ITV -n> iProp)). *)
(*   Variable (kripke : IT → (ITV -n> iProp) → iProp). *)

(*   Program Definition ssubst_valid_fin1 {S : Set} `{!EqDecision S} `{!Finite S} *)
(*     (Ω : S → ty) (ss : interp_scope S) : iProp *)
(*     := ([∗ set] x ∈ (fin_to_set S), *)
(*          (kripke (ss x) (interp_ty (Ω x)))%I). *)

(*   Context (Q : iProp). *)

(*   Definition valid_fin1 {S : Set} `{!EqDecision S} `{!Finite S} (Ω : S → ty) *)
(*     (α : interp_scope S -n> IT) (τ : ty) : iProp := *)
(*     ∀ ss, Q *)
(*           -∗ (ssubst_valid_fin1 Ω ss) *)
(*           -∗ kripke (α ss) (interp_ty τ). *)

(*   Lemma ssubst_valid_fin_empty1 (αs : interp_scope ∅) : *)
(*     ⊢ ssubst_valid_fin1 □ αs. *)
(*   Proof. *)
(*     iStartProof. *)
(*     unfold ssubst_valid_fin1. *)
(*     rewrite fin_to_set_empty. *)
(*     by iApply big_sepS_empty. *)
(*   Qed. *)

(*   Lemma ssubst_valid_fin_app1 *)
(*     {S1 S2 : Set} `{!EqDecision S1} `{!Finite S1} *)
(*     `{!EqDecision S2} `{!Finite S2} *)
(*     `{!EqDecision (S1 + S2)} `{!Finite (S1 + S2)} *)
(*     (Ω1 : S1 → ty) (Ω2 : S2 → ty) *)
(*     (αs : interp_scope (sum S1 S2)) : *)
(*     (ssubst_valid_fin1 (sum_map' Ω1 Ω2) αs) ⊢ *)
(*     (ssubst_valid_fin1 Ω1 (interp_scope_split αs).1) *)
(*     ∗ (ssubst_valid_fin1 Ω2 (interp_scope_split αs).2). *)
(*   Proof. *)
(*     iIntros "H". *)
(*     rewrite /ssubst_valid_fin1 fin_to_set_sum big_sepS_union; first last. *)
(*     { *)
(*       apply elem_of_disjoint. *)
(*       intros [x | x]. *)
(*       - rewrite !elem_of_list_to_set. *)
(*         intros _ H2. *)
(*         apply elem_of_list_fmap_2 in H2. *)
(*         destruct H2 as [y [H2 H2']]; inversion H2. *)
(*       - rewrite !elem_of_list_to_set. *)
(*         intros H1 _. *)
(*         apply elem_of_list_fmap_2 in H1. *)
(*         destruct H1 as [y [H1 H1']]; inversion H1. *)
(*     } *)
(*     iDestruct "H" as "(H1 & H2)". *)
(*     iSplitL "H1". *)
(*     - rewrite big_opS_list_to_set; first last. *)
(*       { *)
(*         apply NoDup_fmap. *)
(*         - intros ??; by inversion 1. *)
(*         - apply NoDup_elements. *)
(*       } *)
(*       rewrite big_sepL_fmap /=. *)
(*       rewrite big_sepS_elements. *)
(*       iFrame "H1". *)
(*     - rewrite big_opS_list_to_set; first last. *)
(*       { *)
(*         apply NoDup_fmap. *)
(*         - intros ??; by inversion 1. *)
(*         - apply NoDup_elements. *)
(*       } *)
(*       rewrite big_sepL_fmap /=. *)
(*       rewrite big_sepS_elements. *)
(*       iFrame "H2". *)
(*   Qed. *)

(*   Lemma ssubst_valid_fin_cons1 {S : Set} `{!EqDecision S} `{!Finite S} *)
(*     (Ω : S → ty) (αs : interp_scope S) τ t : *)
(*     ssubst_valid_fin1 Ω αs ∗ kripke t (interp_ty τ) ⊢ ssubst_valid_fin1 (Ω ▹ τ) (extend_scope αs t). *)
(*   Proof. *)
(*     iIntros "(H & G)". *)
(*     rewrite /ssubst_valid_fin1. *)
(*     rewrite fin_to_set_inc /=. *)
(*     rewrite big_sepS_union; first last. *)
(*     { *)
(*       apply elem_of_disjoint. *)
(*       intros [| x]. *)
(*       - rewrite !elem_of_list_to_set. *)
(*         intros _ H2. *)
(*         apply elem_of_list_fmap_2 in H2. *)
(*         destruct H2 as [y [H2 H2']]; inversion H2. *)
(*       - rewrite !elem_of_list_to_set. *)
(*         intros H1 _. *)
(*         apply elem_of_singleton_1 in H1. *)
(*         inversion H1. *)
(*     } *)
(*     iSplitL "G". *)
(*     - rewrite big_opS_singleton. *)
(*       iFrame "G". *)
(*     - erewrite big_opS_set_map. *)
(*       + iFrame "H". *)
(*       + intros ?? H; by inversion H. *)
(*   Qed. *)

(*   Lemma ssubst_valid_fin_lookup1 {S : Set} `{!EqDecision S} `{!Finite S} *)
(*     (Ω : S → ty) (αs : interp_scope S) x : *)
(*     ssubst_valid_fin1 Ω αs ⊢ kripke (αs x) (interp_ty (Ω x)). *)
(*   Proof. *)
(*     iIntros "H". *)
(*     iDestruct (big_sepS_elem_of_acc _ _ x with "H") as "($ & _)"; *)
(*       first apply elem_of_fin_to_set. *)
(*   Qed. *)

(* End tm_interp_fin. *)
