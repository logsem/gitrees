(* The Lift functor and the interpretation of PCF *)
From Equations Require Import Equations.
From iris.algebra Require cofe_solver.
From iris.proofmode Require Import tactics.
From iris.si_logic Require Import bi.
From gitrees Require Export prelude pcf.lang.

(** * The L functor *)
(* L (A) = A + ▶ L (A)  *)
Definition liftOF (X : ofe) : oFunctor := (X + ▶ ∙).

Global Instance liftOF_contractive X :
  oFunctorContractive (liftOF X).
Proof. apply _. Qed.

Global Instance liftOF_inh X :
  Inhabited (oFunctor_apply (liftOF X) unitO).
Proof. refine (populate (inr $ Next ())). Defined.

Module Export liftF_solution.
  Import cofe_solver.
  Definition lift_result A  `{!Cofe A} :
    solution (liftOF A) := solver.result _.
  Definition liftO A `{!Cofe A} : ofe := (lift_result A).
  Global Instance liftO_cofe A `{!Cofe A} : Cofe (liftO A) := _.


  Definition liftO_unfold {A} `{!Cofe A} : liftO A -n> sumO A (laterO (liftO A)) :=
    ofe_iso_2 (lift_result A).
  Definition liftO_fold {A} `{!Cofe A} : sumO A (laterO (liftO A)) -n> liftO A :=
    ofe_iso_1 (lift_result A).

  Lemma liftO_fold_unfold (A : ofe) `{!Cofe A} (T : liftO A) : liftO_fold (liftO_unfold T) ≡ T.
  Proof. apply ofe_iso_12. Qed.
  Lemma liftO_unfold_fold (A : ofe) `{!Cofe A} (T : sumO A (laterO (liftO A))) :
    liftO_unfold (liftO_fold T) ≡ T.
  Proof. apply ofe_iso_21. Qed.

End liftF_solution.

Program Definition lift_unit `{!Cofe A} : A -n> liftO A :=
  (* @locked (A -n> liftO A) *)
          nosimpl (liftO_fold ◎ (λne x, inl x)).

Program Definition lift_delay `{!Cofe A} : laterO (liftO A) -n> liftO A :=
  (* @locked (laterO (liftO A) -n> liftO A) *)
  nosimpl (liftO_fold ◎ (λne x, inr x)).


(* universal property of liftO *)
Section lift_universal.
Context `{!Cofe A, !Cofe B, !Inhabited B}.

Program Definition lift_up_pre (f : A -n> B) (h : laterO B -n> B)
  (self : liftO A -n> B) : liftO A -n> B := sumO_rec f (h ◎ laterO_ap (Next self)) ◎ liftO_unfold.

Global Instance lift_up_pre_contractive (f : A -n> B) (h : laterO B -n> B) :
  Contractive (lift_up_pre f h).
Proof.
  unfold lift_up_pre.
  intros n self1 self2 Hself.
  f_equiv. f_equiv. f_equiv. f_equiv. by eapply Next_contractive.
Qed.

Program Definition lift_up (f : A -n> B) (h : laterO B -n> B) : liftO A -n> B :=
  fixpoint (lift_up_pre f h).

Lemma lift_up_unfold f h x :
  lift_up f h x ≡ sumO_rec f (h ◎ later_ap (Next (lift_up f h))) (liftO_unfold x).
Proof. apply (fixpoint_unfold (lift_up_pre f h) _). Qed.

Opaque later_ap.
Global Instance lift_up_ne n :
  Proper (dist n ==> dist n ==> dist n) lift_up.
Proof.
  induction n.
  { intros f1 f2 Hf h1 h2 Hh x.
    rewrite !lift_up_unfold. f_equiv. f_equiv; eauto.
    f_equiv; eauto. f_equiv. apply Next_contractive, dist_later_0. }
  intros f1 f2 Hf h1 h2 Hh x.
  rewrite !lift_up_unfold.
  f_equiv; eauto. f_equiv; eauto. f_equiv; eauto.
  f_equiv. eapply Next_contractive. apply dist_later_S.
  eapply IHn; eapply dist_le; eauto.
Qed.

Global Instance lift_up_proper :
  Proper ((≡) ==> (≡) ==> (≡)) lift_up.
Proof.
  intros f1 f2 Hf h1 h2 Hh x.
  eapply equiv_dist=>n.
  eapply lift_up_ne, equiv_dist; eauto.
Qed.

Lemma lift_up_red_now (f : A -n> B) (h : laterO B -n> B) a :
  lift_up f h (lift_unit a) ≡ f a.
Proof.
  rewrite lift_up_unfold.
  rewrite /lift_unit; unlock.
  rewrite liftO_unfold_fold. simpl. done.
Qed.

Lemma lift_up_red_later (f : A -n> B) (h : laterO B -n> B) lb :
  lift_up f h (lift_delay lb) ≡ h (later_ap (Next (lift_up f h)) lb).
Proof.
  rewrite lift_up_unfold.
  rewrite /lift_delay; unlock.
  rewrite liftO_unfold_fold. simpl. done.
Qed.

End lift_universal.

Global Instance liftO_inhabited (A : ofe) `{!Cofe A} `{!Inhabited A} : Inhabited (liftO A).
Proof.
  refine (populate (lift_unit _)).
  refine (inhabitant).
Defined.

Program Definition lift_tick `{!Cofe A} : liftO A -n> liftO A :=
  lift_delay ◎ NextO.

Definition lift_map `{!Cofe A, !Cofe B, !Inhabited B} : (A -n> B) → (liftO A -n> liftO B) :=
  λ f, lift_up (lift_unit ◎ f) (@lift_delay B _).

#[export] Instance lift_map_ne `{!Cofe A, !Cofe B, !Inhabited B} n :
  Proper (dist n ==> dist n) (lift_map (A:=A) (B:=B)).
Proof. unfold lift_map; solve_proper. Qed.


(** * Interpreting PCF *)
(* Interpretation of types *)
Fixpoint interp_ty (t : ty) :=
  match t with
  | tnat => liftO natO
  | tarr t1 t2 => interp_ty t1 -n> interp_ty t2
  end.
Arguments interp_ty : simpl never.

#[export] Instance interp_type_cofe (τ : ty) : Cofe (interp_ty τ).
Proof.
  induction τ; simpl; apply _.
Qed.

#[export] Instance interp_type_inhabited (τ : ty) : Inhabited (interp_ty τ).
Proof.
  induction τ; simpl; apply _.
Defined.

Opaque later_ap.
Program Definition dom_ty_alg (τ1 τ2 : ty) (interp2 : laterO (interp_ty τ2) -n> interp_ty τ2) :=
  λne alg (x : laterO (interp_ty τ1 -n> interp_ty τ2)), interp2 (laterO_ap alg (Next x)).
Next Obligation. solve_proper.  Qed.
Next Obligation. solve_contractive. Qed.

Program Fixpoint ty_later_alg (τ : ty) : laterO (interp_ty τ) -n> interp_ty τ :=
  match τ with
  | tnat => lift_delay
  | tarr t1 t2 =>
    λne (f : laterO (interp_ty t1 -n> interp_ty t2)) x, ty_later_alg t2 (laterO_ap f (Next x))
  end.
Opaque later_ap.
Next Obligation. solve_proper. Defined.
Next Obligation. solve_proper. Defined.
Transparent later_ap.

Program Definition interp_ty_tick {τ : ty} : interp_ty τ -n> interp_ty τ :=
  ty_later_alg τ ◎ NextO.

(* Interpretation of contexts - just take products *)
Fixpoint interp_ctx (C : ctx) : ofe :=
  match C with
  | [] => unitO
  | τ::C => prodO (interp_ty τ) (interp_ctx C)
  end.

#[export] Instance interp_ctx_cofe C : Cofe (interp_ctx C).
Proof.
  induction C; simpl; eapply _.
Qed.

#[export] Instance interp_ctx_inhab C : Inhabited (interp_ctx C).
Proof.
  induction C; simpl; eapply _.
Defined.

(* Interpreting variables in a context *)
Equations interp_var {C : ctx} {τ : ty} (v : var C τ) : interp_ctx C → interp_ty τ :=
interp_var (C:=τ::_)     Vz D := fst D;
interp_var (C:=_::C) (Vs v) D := interp_var v (snd D).

Global Instance interp_var_ne C (τ : ty) (v : var C τ) : NonExpansive (interp_var v).
Proof.
  intros n D1 D2 HD12. induction v; simp interp_var.
  - by f_equiv.
  - eapply IHv. by f_equiv.
Qed.
Global Instance interp_var_proper C (τ : ty) (v : var C τ) : Proper ((≡) ==> (≡)) (interp_var v).
Proof. apply ne_proper. apply _. Qed.

(* Finally, interpretation of terms *)
(* DF: had to take out out of the main Equations clauses to make it typecheck *)
Program Definition interp_lam_body {C τ1 τ2}
        (int : interp_ctx (τ1::C) -n> interp_ty τ2)
  : interp_ctx C -n> interp_ty (tarr τ1 τ2) :=
  λne D x, int (x, D).
Solve Obligations with solve_proper.

Program Definition interp_app {C τ1 τ2}
        (int1 : interp_ctx C -n> interp_ty (tarr τ1 τ2))
        (int2 : interp_ctx C -n> interp_ty τ1) : interp_ctx C -n> interp_ty τ2 :=
  λne D, int1 D (int2 D).
Solve Obligations with solve_proper.

(* XXX: we put those out at separate definitions to make sure
that we use _the same_ proof of non-expansiveness... maybe
using SProp of Coq will render this useless? *)
Program Definition succ_ne : natO -n> natO := λne n, S n.
Program Definition pred_ne : natO -n> natO := λne n, pred n.

Program Definition interp_succ {C} (int : interp_ctx C -n> interp_ty tnat)
  : interp_ctx C -n> interp_ty tnat :=
  λne D, lift_map succ_ne (int D).
Solve Obligations with solve_proper.

Program Definition interp_pred {C} (int : interp_ctx C -n> interp_ty tnat)
  : interp_ctx C -n> interp_ty tnat :=
  λne D, lift_map pred_ne (int D).
Solve Obligations with solve_proper.

(* all such "tick" functions, that arise from ▷-algebras, are contractive *)
#[export] Instance interp_ty_tick_contractive (τ : ty) : Contractive (@interp_ty_tick τ).
Proof. solve_contractive. Qed.

Program Definition interp_Y_pre {C} (τ : ty)
  : laterO (interp_ctx C -n> interp_ty (tarr (tarr τ τ) τ)) -n>
            interp_ctx C -n> interp_ty (tarr (tarr τ τ) τ) :=
  λne self D f, let self' := laterO_ap self (NextO D) in
           ty_later_alg τ $ laterO_map f (laterO_ap self' (NextO f)).
Opaque later_ap.
Next Obligation.
  intros C τ self D n f g Hfg. simpl.
  f_equiv.
  etrans.
  { by eapply laterO_map_contractive, dist_dist_later. }
  by repeat f_equiv.
Qed.
Next Obligation.
  intros C τ self D n f g Hfg.
  simpl. f_equiv.
  etrans.
  { by eapply laterO_map_contractive, dist_dist_later. }
  by repeat f_equiv.
Qed.
Next Obligation.
  intros C τ self D n f g Hfg.
  simpl. f_equiv.
  etrans.
  { by eapply laterO_map_contractive, dist_dist_later. }
  by repeat f_equiv.
Qed.

Definition interp_Y {C} {τ : ty} : interp_ctx C -n> interp_ty (tarr (tarr τ τ) τ)
  := mmuu (interp_Y_pre τ).

Program Definition interp_unfold {C} {τ : ty} (int : interp_ctx C -n> interp_ty (tarr τ τ)) : interp_ctx C -n> interp_ty τ := λne Δ,
  interp_Y Δ (int Δ).
Next Obligation. solve_proper. Qed.

Equations interp_tm {C : ctx} {τ : ty} (M : tm C τ) : interp_ctx C -n> interp_ty τ :=
interp_tm (Num n) := λne _, lift_unit n;
interp_tm (Var v) := OfeMor (interp_var v);
interp_tm (Lam N) := interp_lam_body (interp_tm N);
interp_tm (App f a) := interp_app (interp_tm f) (interp_tm a);
interp_tm (Succ M) := interp_succ (interp_tm M);
interp_tm (Pred M) := interp_pred (interp_tm M);
interp_tm (Y M) := interp_unfold (interp_tm M)
.

Equations interp_rens_ctx {C D : ctx}
          (E : interp_ctx D) (s : rens C D) : interp_ctx C :=
  interp_rens_ctx (C:=[]) E s := tt : interp_ctx [];
  interp_rens_ctx (C:=_::_) E s :=
    (interp_var (hd_ren s) E, interp_rens_ctx E (tl_ren s)).

Equations interp_subs_ctx {C D : ctx}
          (E : interp_ctx D) (s : subs C D) : interp_ctx C :=
  interp_subs_ctx (C:=[]) E s := tt : interp_ctx [];
  interp_subs_ctx (C:=_::_) E s :=
    (interp_tm (hd_sub s) E, interp_subs_ctx E (tl_sub s)).

(** * Properties of the interpretation *)

(** ** Facts about Y *)
(* Lemma 4.1 in PMB *)
Lemma interp_Y_app {C} {τ : ty} (D : interp_ctx C) (M : interp_ty τ -n> interp_ty τ) :
  interp_Y D M ≡ interp_ty_tick $ M (interp_Y D M).
Proof.
  rewrite {1}/interp_Y.
  etrans.
  { eapply (mmuu_unfold (interp_Y_pre τ) _ _). }
  rewrite {1}/interp_Y_pre /=.
  f_equiv.
  Transparent later_ap.
  rewrite /later_ap /=.
  rewrite /later_map/=.
  by rewrite /interp_Y.
Qed.

#[export] Instance interp_Y_contractive {C : ctx} {τ : ty} (E : interp_ctx C) : Contractive (@interp_Y C τ E).
Proof.
  intros n. induction n=> M M' HM.
  - rewrite interp_Y_app (interp_Y_app E M').
    eapply interp_ty_tick_contractive, dist_later_0.
  - rewrite interp_Y_app (interp_Y_app E M').
    apply dist_later_S in HM.
    eapply interp_ty_tick_contractive, dist_later_S.
    f_equiv; eauto. eapply IHn. by eapply dist_dist_later.
Qed.

Lemma interp_Y_const (τ: ty) {C D : ctx} (E : interp_ctx C) (E' : interp_ctx D) :
  @interp_Y C τ E ≡ interp_Y E'.
Proof.
  intro M. eapply equiv_dist=>n.
  induction n.
  { rewrite interp_Y_app. rewrite (interp_Y_app E').
    eapply interp_ty_tick_contractive, dist_later_0. }
  rewrite interp_Y_app. rewrite (interp_Y_app E').
  eapply interp_ty_tick_contractive, dist_later_S.
  by f_equiv.
Qed.

(** ** [lift_map] properties *)
Lemma lift_map_unit `{!Cofe A, !Cofe B, !Inhabited B} (f : A -n> B) a :
  lift_map f (lift_unit a) ≡ lift_unit (f a).
Proof.
  by rewrite lift_up_red_now.
Qed.

Lemma lift_map_delay `{!Cofe A, !Cofe B, !Inhabited B} (f : A -n> B) β :
  lift_map f (lift_delay β) ≡ lift_delay (later_map (lift_map f) (β : later (liftO A))).
Proof.
  by rewrite lift_up_red_later.
Qed.

(* Apply [interp_ty_tick] k times *)
Definition ty_tick_k (k : nat) {τ : ty} : interp_ty τ → interp_ty τ :=
  Nat.iter k interp_ty_tick.

Global Instance ty_tick_k_ne k τ : NonExpansive (@ty_tick_k k τ).
Proof.
  intros n. induction k; intros x y Hxy; simpl; eauto.
  f_equiv. eapply Next_contractive.
  eapply dist_dist_later. by eapply IHk.
Qed.

Global Instance ty_tick_k_proper k τ : Proper ((≡) ==> (≡)) (@ty_tick_k k τ).
Proof.
  induction k; intros x y Hxy; simpl; eauto.
  solve_proper.
Qed.

Lemma ty_tick_k_lift_map k (f : natO -n> natO) (x : interp_ty tnat) :
  lift_map f (ty_tick_k k x) ≡ ty_tick_k k ((lift_map f x) : interp_ty tnat).
Proof.
  revert f. induction k=>f; simpl; eauto.
  rewrite lift_map_delay.
  simpl. f_equiv. f_equiv. eapply IHk.
Qed.


(** ** Interactions of substitutions, weakenings, and interpretations of contexts, variables, terms *)
Global Instance interp_rens_ctx_proper C D :
  Proper ((≡) ==> (≡) ==> (≡)) (@interp_rens_ctx C D).
Proof.
  intros E E' HE s1 s2 Hs.
  induction C as [|τ' C]; simp interp_rens_ctx; auto.
  f_equiv.
  - unfold hd_ren; by rewrite Hs HE.
  - apply IHC. intros ? v. unfold tl_ren; by rewrite Hs.
Qed.
Global Instance interp_subs_ctx_proper C D :
  Proper ((≡) ==> (≡) ==> (≡)) (@interp_subs_ctx C D).
Proof.
  intros E E' HE s1 s2 Hs.
  induction C as [|τ' C]; simp interp_subs_ctx; auto.
  f_equiv.
  - unfold hd_sub; by rewrite Hs HE.
  - apply IHC. intros ? v. unfold tl_sub; by rewrite Hs.
Qed.

Ltac simplify_tm :=
  repeat progress first [ simp interp_tm | unfold subst1
                          | simp subst_tm | simp interp_var ]; simpl.


Lemma interp_rens_ctx_tl_ren {C D τ} x E (r : rens C D) :
  interp_rens_ctx ((x, E) : interp_ctx (τ::D)) (tl_ren (rens_lift r))
                  ≡ interp_rens_ctx E r.
Proof.
  induction C as [|τ' C]; simp interp_rens_ctx; eauto.
  f_equiv.
  { unfold hd_ren, tl_ren. simp rens_lift interp_var.
    done. }
  { rewrite -IHC. f_equiv. clear.
    intros τ2 v. dependent elimination v;
                   unfold hd_ren, tl_ren; simp rens_lift; auto. }
Qed.


Lemma interp_tm_ren {Γ D : ctx} {τ} (M : tm Γ τ) (r : rens Γ D) :
  ∀ (E : interp_ctx D),
    interp_tm (ren_tm M r) E ≡ interp_tm M (interp_rens_ctx E r).
Proof.
  revert D r. induction M=>D r E; simp ren_tm interp_tm ; first done.
  all: try by (simp interp_tm; repeat intro; simpl; f_equiv; eauto).
  - simpl. revert r.
    induction v=>r.
    + simp interp_var interp_rens_ctx. done.
    + simp interp_var interp_rens_ctx. simpl.
      apply (IHv (tl_ren r)).
  - simp interp_tm. intros x. simpl.
    rewrite IHM. f_equiv.
    clear.
    destruct Γ as [|τ' Γ]; first done.
    rewrite interp_rens_ctx_equation_2.
    simp interp_var. f_equiv.
    by rewrite interp_rens_ctx_tl_ren.
  - simp interp_tm. simpl. rewrite IHM.
    f_equiv. eapply interp_Y_const.
Qed.

Lemma interp_rens_ctx_id {Γ} (E : interp_ctx Γ) :
  interp_rens_ctx E (@idren Γ) ≡ E.
Proof.
  induction Γ as [|τ' Γ]; simp interp_rens_ctx.
  { by destruct E. }
  destruct E as [x E]. simp interp_var. simpl.
  f_equiv.
  trans (interp_rens_ctx ((x, E) : interp_ctx (τ'::Γ)) (tl_ren (rens_lift idren))).
  { f_equiv. intros ? v. unfold tl_ren.
    reflexivity. }
  rewrite interp_rens_ctx_tl_ren.
  apply IHΓ.
Qed.

Lemma interp_subs_ctx_tl_sub {Γ D τ} x E (s : subs Γ D) :
  interp_subs_ctx ((x, E) : interp_ctx (τ::D)) (tl_sub (subs_lift s))
                  ≡ interp_subs_ctx E s.
Proof.
  induction Γ as [|τ' Γ]; simp interp_subs_ctx; first done.
  f_equiv.
  { unfold hd_sub, tl_sub. simp subs_lift interp_var.
    unfold tm_lift. rewrite interp_tm_ren. f_equiv.
    trans (interp_rens_ctx ((x, E) : interp_ctx (τ::D)) (tl_ren (rens_lift idren))).
    { f_equiv. intros ? v. unfold tl_ren.
      simp rens_lift idren. done. }
    rewrite interp_rens_ctx_tl_ren.
    apply interp_rens_ctx_id. }
  { rewrite -IHΓ. f_equiv. clear.
    intros τ2 v. dependent elimination v;
                   unfold hd_sub, tl_sub; simp subs_lift; auto. }
Qed.

Lemma interp_tm_subst {Γ D : ctx} {τ} (M : tm Γ τ) (s : subs Γ D) :
  ∀ (E : interp_ctx D),
    interp_tm (subst_tm M s) E ≡ interp_tm M (interp_subs_ctx E s).
Proof.
  revert D s. induction M=>D s E; simp subst_tm interp_tm ; first done.
  all: try by (simp interp_tm; repeat intro; simpl; f_equiv; eauto).
  - simpl. revert s.
    induction v=>r.
    + simp interp_var interp_subs_ctx. done.
    + simp interp_var interp_subs_ctx. simpl.
      apply (IHv (tl_sub r)).
  - simp interp_tm. intros x. simpl.
    rewrite IHM. f_equiv.
    clear.
    destruct Γ as [|τ' Γ]; first done.
    rewrite interp_subs_ctx_equation_2.
    simp interp_var. f_equiv.
    { unfold hd_sub. simp subs_lift. simpl. done. }
    by rewrite interp_subs_ctx_tl_sub.
  - simp interp_tm. simpl. rewrite IHM.
    f_equiv. eapply interp_Y_const.
Qed.

Lemma interp_subs_ctx_id {Γ} (E : interp_ctx Γ) :
  interp_subs_ctx E (@idsub Γ) ≡ E.
Proof.
  induction Γ as [|τ' Γ]; simp interp_subs_ctx.
  { by destruct E. }
  destruct E as [x E].
  unfold hd_sub, idsub. simp interp_tm ; simpl; simp interp_var.
  f_equiv; first try done.
  trans (interp_subs_ctx ((x, E) : interp_ctx (τ'::Γ)) (tl_sub (subs_lift idsub))).
  { f_equiv. intros ? v. unfold tl_sub.
    reflexivity. }
  rewrite interp_subs_ctx_tl_sub.
  apply IHΓ.
Qed.


(** Finally, we can prove soundness of the interpretation *)
Lemma interp_tm_step {C : ctx} {τ : ty} (M N : tm C τ) k :
  step M k N → interp_tm M ≡ OfeMor (ty_tick_k k) ◎ interp_tm N.
Proof.
  induction 1; intro D.
  - simplify_tm.
    rewrite (interp_tm_subst). f_equiv.
    simp interp_subs_ctx. f_equiv; first done.
    rewrite -{1}(interp_subs_ctx_id D). f_equiv.
    intros ? x. reflexivity.
  - simplify_tm. eapply interp_Y_app.
  - simplify_tm. rewrite lift_map_unit. reflexivity.
  - simplify_tm.  specialize (IHstep D). simpl.
    rewrite IHstep.
    by rewrite ty_tick_k_lift_map.
  - simplify_tm. rewrite lift_map_unit. reflexivity.
  - simplify_tm.  specialize (IHstep D). simpl.
    rewrite IHstep.
    by rewrite ty_tick_k_lift_map.
  - simplify_tm. specialize (IHstep D (interp_tm N D)).
    rewrite IHstep. simpl. clear IHstep H.
    induction k; simpl; eauto.
    f_equiv. f_equiv. eapply IHk.
Qed.

Lemma interp_tm_step_clos {C : ctx} {τ : ty} (M N : tm C τ) k :
  step_clos M k N → interp_tm M ≡ OfeMor (ty_tick_k k) ◎ interp_tm N.
Proof.
  induction 1; intro D.
  - simpl. done.
  - simpl. rewrite (interp_tm_step _ _ _ _ _) //.
    simpl. specialize (IHstep_clos D). simpl in *.
    rewrite IHstep_clos. rewrite /ty_tick_k.
    rewrite Nat.iter_add /= //.
Qed.

(** * Injectivity/invertibility for constructors *)
(** XXX: There's got to be a better way of showing this.. *)
Lemma lift_unit_delay_ne {A} `{!Cofe A} (α : laterO (liftO A)) (x : A) :
  (lift_unit x ≡ lift_delay α ⊢@{siPropI} False)%I.
Proof.
  trans (liftO_unfold (lift_unit x) ≡ liftO_unfold (lift_delay α) : siProp)%I.
  { iIntros "H". by iRewrite "H". }
  simpl. rewrite !liftO_unfold_fold.
  rewrite /internal_eq /bi_internal_eq_internal_eq /=.
  siProp_primitive.unseal.
  rewrite /siprop.siProp_internal_eq_def /=.
  rewrite /siPropI /bi_entails /=.
  split=>n. rewrite /siProp_holds /=.
  inversion 1.
Qed.

Lemma lift_delay_inj {A} `{!Cofe A} (α β : laterO (liftO A)) :
  (lift_delay α ≡ lift_delay β ⊢@{siPropI} α ≡ β)%I.
Proof.
  trans (liftO_unfold (lift_delay α) ≡ liftO_unfold (lift_delay β) : siProp)%I.
  { iIntros "H". by iRewrite "H". }
  simpl. rewrite !liftO_unfold_fold.
  rewrite /internal_eq /bi_internal_eq_internal_eq /=.
  siProp_primitive.unseal.
  rewrite /siprop.siProp_internal_eq_def /=.
  rewrite /siPropI /bi_entails /=.
  split=>n. rewrite /siProp_holds /=.
  inversion 1; eauto.
Qed.

Lemma lift_unit_inj {A} `{!Cofe A} (x y : A) :
  (lift_unit x ≡ lift_unit y ⊢@{siPropI} x ≡ y)%I.
Proof.
  trans (liftO_unfold (lift_unit x) ≡ liftO_unfold (lift_unit y) : siProp)%I.
  { iIntros "H". by iRewrite "H". }
  simpl. rewrite !liftO_unfold_fold.
  rewrite /internal_eq /bi_internal_eq_internal_eq /=.
  siProp_primitive.unseal.
  rewrite /siprop.siProp_internal_eq_def /=.
  rewrite /siPropI /bi_entails /=.
  split=>n. rewrite /siProp_holds /=.
  inversion 1; eauto.
Qed.

#[global] Opaque lift_unit lift_delay.
