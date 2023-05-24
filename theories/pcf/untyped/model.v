(* Untyped/unityped model through a universal domain *)
From Equations Require Import Equations.
From iris.algebra Require cofe_solver.
From iris.base_logic Require Export base_logic.
From iris.prelude Require Import options.
From iris.si_logic Require Import bi siprop.
From iris.proofmode Require Import tactics.
From gitrees Require Import prelude pcf.lang.


Opaque laterO_map.

(*** The universal domain *)
(* Defining the universal domain.
   In order to define `app', we need
   the domain to have the ▶ -algebra structure.
 *)

Module D_pre.
Definition DOF : oFunctor :=
  ( natO
  + unitO
  + ▶ ∙
  + ▶ (∙ -n> ∙) ).


#[export] Instance DOF_contractive :
  oFunctorContractive (DOF).
Proof. apply _. Qed.

#[export] Instance DOF_inhabited :
  Inhabited (oFunctor_apply (DOF) unitO).
Proof.
  refine (populate _).
  refine (inl (inl (inr (())))).
Defined.

#[export] Instance DOF_cofe T `{!Cofe T, !Cofe A}:
  Cofe (oFunctor_apply (DOF) T).
Proof.
  apply _.
Defined.
End D_pre.

Module Export DF_solution.
  Import D_pre.
  Import cofe_solver.
  Definition D_result :
    solution (DOF)
   := solver.result (DOF).

  Definition D : ofe := (D_result).
  Global Instance D_cofe : Cofe (D) := _.


  Definition D_unfold :
    D -n> sumO (sumO (sumO natO unitO)
                      (laterO D))
                (laterO (D -n> D))
    := ofe_iso_2 (D_result).

  Definition D_fold :
    sumO (sumO (sumO natO unitO)
               (laterO D))
         (laterO (D -n> D)) -n> D
    := ofe_iso_1 (D_result).

  Lemma D_fold_unfold (T : D) :
    D_fold (D_unfold T) ≡ T.
  Proof. apply ofe_iso_12. Qed.
  Lemma D_unfold_fold T :
    D_unfold (D_fold T) ≡ T.
  Proof. apply ofe_iso_21. Qed.

  Definition D_nat (n : nat) : D :=
    D_fold (OfeMor inl (inl (inl n))).
  Definition D_err : D :=
    D_fold (OfeMor inl (inl (inr ()))).
  Definition D_thunk : laterO D -n> D :=
    D_fold ◎ OfeMor inl ◎ OfeMor inr.
  Definition D_arr : laterO (D -n> D) -n> D :=
    D_fold ◎ OfeMor inr.
End DF_solution.

Global Instance D_inhabited : Inhabited D :=
  populate D_err.

Section D_rec.
  Variable (P : ofe).
  Context `{!Cofe P, !Inhabited P}.
  Variable (Perr : P)
           (Pnat : nat → P)
           (Pthunk : laterO D -n> laterO P -n> P)
           (Parr : laterO (D -n> D) -n> laterO (P -n> P) -n> P)
           (Pback : P -n>
                      sumO (sumO (sumO natO unitO)
                                 (laterO P))
                                (laterO (P -n> P))).

  Program Definition D_rec_pre
          (self12 : prodO (D -n> P) (P -n> D))
    : prodO (D -n> P) (P -n> D).
  Proof using P Parr Pback Perr Pnat Pthunk.
    set (self1 := fst self12).
    set (self2 := snd self12).
    simple refine (_,_).
    { refine (_ ◎ D_unfold).
      repeat refine (sumO_rec _ _).
      - simple refine (λne n, Pnat n).
      - simple refine (λne _, Perr).
      - simple refine (λne t, Pthunk t (laterO_map self1 t)).
        solve_proper.
      - simple refine (λne lf, Parr lf (laterO_map _ lf)).
        + simple refine (λne (f : D -n> D) p,
                   self1 (f (self2 p))).
          all: solve_proper.
        + repeat intro. repeat f_equiv; eauto. }
    { refine (_ ◎ Pback).
      repeat refine (sumO_rec _ _).
      - refine (OfeMor D_nat).
      - refine (λne _, D_err).
      - refine (D_thunk ◎ laterO_map self2).
      - refine (D_arr ◎ laterO_map _).
        simple refine (λne (f : P -n> P) t,
                 self2 (f (self1 t))).
        all: solve_proper. }
  Defined.

  (* TODO: look into dist_later_prod *)
  Instance D_rec_pre_contractive : Contractive D_rec_pre.
  Proof.
    rewrite /D_rec_pre.
    intros n [h1 k1] [h2 k2] Hhk.
    repeat (f_contractive
            || f_equiv
            || destruct Hhk as [Hh Hk]); eauto.
    { repeat intro; cbn. f_equiv.
      eapply laterO_map_contractive.
      destruct n; [ by apply dist_later_0 | apply dist_later_S ].
      apply (Hh n). lia. }
    { repeat intro. simpl. f_equiv.
      eapply laterO_map_contractive.
      destruct n; [ by apply dist_later_0 | apply dist_later_S ].
      do 2 intro; simpl. f_equiv; eauto.
      + apply (Hh n). lia.
      + repeat f_equiv; eauto.
        apply (Hh n). lia.
    }
    { do 2 intro; simpl.
      repeat f_equiv; eauto. }
  Qed.

  Definition D_rec : prodO (D -n> P) (P -n> D) :=
    fixpoint D_rec_pre.

  Definition D_rec_1 : D -n> P := fst D_rec.
  Definition D_rec_2 : P -n> D := snd D_rec.

  Lemma D_rec_unfold :
    D_rec ≡ D_rec_pre D_rec.
  Proof. apply (fixpoint_unfold D_rec_pre). Qed.
  Lemma D_rec_1_unfold t :
    D_rec_1 t ≡ (D_rec_pre D_rec).1 t.
  Proof. apply (fixpoint_unfold D_rec_pre). Qed.

  Lemma D_rec_1_nat (n : nat) :
    D_rec_1 (D_nat n) ≡ Pnat n.
  Proof.
    rewrite D_rec_1_unfold /D_nat.
    rewrite /D_rec_pre.
    cbn-[sumO_rec].
    (* Here we need to be careful not to simplify sum_rec, which will
    unfold into a `match` and we wouldnt be able to use setoid
    rewriting. *)
    rewrite D_unfold_fold.
    simpl. reflexivity.
  Qed.

  Lemma D_rec_1_err :
    D_rec_1 D_err ≡ Perr.
  Proof.
    rewrite D_rec_1_unfold /D_nat.
    rewrite /D_rec_pre.
    cbn-[sumO_rec].
    rewrite D_unfold_fold.
    simpl. reflexivity.
  Qed.

  Program Definition sandwich : (D -n> D) -n> P -n> P :=
    λne f, D_rec_1 ◎ f ◎ D_rec_2.
  Next Obligation. solve_proper. Defined.

  Lemma D_rec_1_arr f :
    D_rec_1 (D_arr f) ≡ Parr f (laterO_map sandwich f).
  Proof.
    rewrite D_rec_1_unfold /D_nat.
    rewrite /D_rec_pre.
    cbn-[sumO_rec].
    rewrite D_unfold_fold.
    simpl. f_equiv.
    unfold sandwich. repeat f_equiv.
    do 2 intro. simpl. reflexivity.
  Qed.

  Lemma D_rec_1_thunk f :
    D_rec_1 (D_thunk f) ≡ Pthunk f (laterO_map D_rec_1 f).
  Proof.
    rewrite D_rec_1_unfold /D_nat.
    rewrite /D_rec_pre.
    cbn-[sumO_rec].
    by rewrite D_unfold_fold.
  Qed.


End D_rec.

Global Instance D_rec_ne {P : ofe} `{!Cofe P, !Inhabited P} n :
  Proper (dist n ==> (pointwise_relation _ (dist n)) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (D_rec P).
Proof.
  intros e1 e2 He nt1 nt2 Hnt th1 th2 Hth a1 a2 Ha b1 b2 Hb.
  unfold D_rec.
  eapply fixpoint_ne. intros [h k].
  unfold D_rec_pre. repeat f_equiv; eauto.
  all: repeat intro; simpl; repeat f_equiv; eauto.
Qed.
Global Instance D_rec_1_ne {P : ofe} `{!Cofe P, !Inhabited P} n :
  Proper (dist n ==> (pointwise_relation _ (dist n)) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (D_rec_1 P).
Proof. unfold D_rec_1. solve_proper. Qed.
Global Instance D_rec_proper {P : ofe} `{!Cofe P, !Inhabited P} :
  Proper ((≡) ==> (pointwise_relation _ (≡)) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (D_rec P).
Proof.
  intros e1 e2 He nt1 nt2 Hnt th1 th2 Hth a1 a2 Ha b1 b2 Hb.
  unfold D_rec.
  eapply fixpoint_proper. intros [h k].
  unfold D_rec_pre. repeat f_equiv; eauto.
  all: repeat intro; simpl; repeat f_equiv; eauto.
Qed.
Global Instance D_rec_1_proper {P : ofe} `{!Cofe P, !Inhabited P} :
  Proper ((≡) ==> (pointwise_relation _ (≡)) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (D_rec_1 P).
Proof. unfold D_rec_1. solve_proper. Qed.

(* ▷-algebra *)
Definition D_tick := D_thunk ◎ NextO.
Definition D_tick_n n := Nat.iter n D_tick.
Global Instance D_tick_n_ne n : NonExpansive (D_tick_n n).
Proof. induction n; solve_proper. Qed.
Global Instance D_tick_proper n : Proper ((≡) ==> (≡)) (D_tick_n n).
Proof. induction n; solve_proper. Qed.

Lemma D_tick_n_O α : D_tick_n 0 α = α.
Proof. reflexivity. Qed.

Lemma D_tick_n_S k α : D_tick_n (S k) α = D_tick (D_tick_n k α).
Proof. reflexivity. Qed.

Lemma D_tick_add k l α : D_tick_n (k + l) α = D_tick_n k (D_tick_n l α).
Proof.
  induction k; first done.
  cbn[plus]. by rewrite !D_tick_n_S IHk.
Qed.

Global Instance D_tick_inj k : Inj (dist k) (dist (S k)) D_tick.
Proof.
  intros x y. intros H1.
  assert (D_unfold (D_tick x) ≡{S k}≡ D_unfold (D_tick y)) as H2.
  { by rewrite H1. }
  revert H2. rewrite /D_tick /=.
  rewrite !D_unfold_fold. intros H2.
  apply (Next_inj (S k) x y); last lia.
  by eapply inr_ne_inj, inl_ne_inj.
Qed.

Global Instance D_tick_contractive : Contractive D_tick.
Proof. solve_contractive. Qed.

Section D_destructors.
  Definition ignore1 {A : ofe} : A -n> D :=
    λne _, D_err.
  Definition ignore2 {A B : ofe} : A -n> B -n> D :=
    λne _ _, D_err.
  Program Definition get_nat (f : nat -> D) : D -n> D
    := D_rec_1 D D_err f (λne _, D_thunk) ignore2 D_unfold.
  Program Definition get_fun (f : laterO (D -n> D) -n> D) : D -n> D
    := D_rec_1 D D_err ignore1 (λne _, D_thunk) (λne g _, f g) D_unfold.
  Solve Obligations with solve_proper.

  Lemma get_nat_nat f n : get_nat f (D_nat n) ≡ f n.
  Proof. by rewrite D_rec_1_nat. Qed.
  Lemma get_nat_tick f t : get_nat f (D_tick t) ≡ D_tick (get_nat f t).
  Proof. by rewrite D_rec_1_thunk. Qed.
  Lemma get_nat_tick_n f t n : get_nat f (D_tick_n n t) ≡ D_tick_n n (get_nat f t).
  Proof.
    induction n; first reflexivity.
    by rewrite get_nat_tick IHn.
  Qed.
  Lemma get_nat_fun f t : get_nat f (D_arr t) ≡ D_err.
  Proof. by rewrite D_rec_1_arr. Qed.

  Lemma get_fun_fun f g : get_fun f (D_arr g) ≡ f g.
  Proof. by rewrite D_rec_1_arr. Qed.
  Lemma get_fun_tick f t : get_fun f (D_tick t) ≡ D_tick (get_fun f t).
  Proof. by rewrite D_rec_1_thunk. Qed.
  Lemma get_fun_tick_n f t n : get_fun f (D_tick_n n t) ≡ D_tick_n n (get_fun f t).
  Proof.
    induction n; first reflexivity.
    by rewrite get_fun_tick IHn.
  Qed.

End D_destructors.

Global Instance get_nat_ne n :
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (get_nat ).
Proof. unfold get_nat. solve_proper. Qed.
Global Instance get_nat_proper :
  Proper ((≡@{natO -n> D}) ==> (≡)) (get_nat ).
Proof. unfold get_nat. solve_proper. Qed.
Global Instance get_fun_ne : NonExpansive get_fun.
Proof.
  unfold get_fun.
  intros n F1 F2 HF. f_equiv.
  intros g ?; simpl. by f_equiv.
Qed.
Global Instance get_fun_ne2 : NonExpansive2 get_fun.
Proof.
  unfold get_fun.
  intros n F1 F2 HF x1 x2 Hx. repeat f_equiv; eauto.
  intros g ?; simpl. by f_equiv.
Qed.

Global Instance get_fun_proper :
  Proper ((≡) ==> (≡)) (get_fun).
Proof.
  unfold get_fun.
  intros F1 F2 HF. f_equiv.
  intros g ?; simpl. by f_equiv.
Qed.

Program Definition APP : D -n> D -n> D := λne f1 f2,
    get_fun
      (λne g, D_thunk $ laterO_ap g (Next f2))
      f1.
Next Obligation.
  intros _ f2 n g1 g2 Hg.
  by repeat f_equiv.
Qed.
Next Obligation.
  repeat intro; cbn-[D_thunk  D_arr mmuu get_nat get_fun];
  repeat f_equiv; eauto. intro g. simpl.
  by repeat f_equiv.
Qed.
Next Obligation.
  repeat intro; cbn-[D_thunk  D_arr mmuu get_nat get_fun];
  repeat f_equiv; eauto.
Qed.

Definition SUCC : D -n> D := get_nat (λ n, D_nat (S n)).
Definition PRED : D -n> D := get_nat (λ n, D_nat (pred n)).

(** ** injectivety/inversion lemmas *)
Global Instance D_nat_inj n : Inj (=) (dist n) D_nat.
Proof.
  intros x y. intros H1.
  assert (D_unfold (D_nat x) ≡{n}≡ D_unfold (D_nat y)) as H2.
  { by rewrite H1. }
  revert H2. rewrite /D_nat /=.
  rewrite !D_unfold_fold. intros H2.
  unfold_leibniz.
  eapply discrete_iff; first apply _.
  by eapply inl_ne_inj, inl_ne_inj, inl_ne_inj.
Qed.

Lemma D_thunk_inj' a b : D_thunk a ≡ D_thunk b ⊢@{siProp} a ≡ b.
Proof.
  iIntros "H1".
  iAssert (D_unfold (D_thunk a) ≡ D_unfold (D_thunk b))%I with "[H1]" as "H2".
  { by iRewrite "H1". }
  rewrite /D_thunk /=.
  rewrite !D_unfold_fold.
  iPoseProof (sum_equivI with "H2") as "H2".
  iPoseProof (sum_equivI with "H2") as "H2".
  done.
Qed.
Lemma D_nat_inj' n m : D_nat n ≡ D_nat m ⊢ (⌜n = m⌝ : siProp).
Proof.
  iIntros "H1".
  iAssert (D_unfold (D_nat n) ≡ D_unfold (D_nat m))%I with "[H1]" as "H2".
  { by iRewrite "H1". }
  rewrite /D_nat /=.
  rewrite !D_unfold_fold.
  iDestruct "H2" as "%Hfoo".
  unfold_leibniz. iPureIntro.
  by eapply inl_equiv_inj, inl_equiv_inj, inl_equiv_inj.
Qed.

Lemma D_nat_not_thunk n α :
  (D_nat n ≡ D_thunk α ⊢ False : siProp).
Proof.
  iIntros "H1".
  iAssert (D_unfold (D_nat n) ≡ D_unfold (D_thunk α))%I with "[H1]" as "H2".
  { by iRewrite "H1". }
  rewrite /D_nat /D_thunk /=.
  rewrite !D_unfold_fold.
  iDestruct "H2" as "%Hfoo".
  exfalso.
  inversion Hfoo; simplify_eq/=.
  by inversion H1.
Qed.

Ltac simpl_me := cbn-[D_thunk  D_arr mmuu get_nat get_fun APP].

Ltac solve_proper_ish :=
  repeat intro; cbn-[D_thunk  D_arr mmuu get_nat get_fun];
  repeat f_equiv; eauto.

Lemma APP_tick_l α β : (APP (D_tick α) β) ≡ D_tick (APP α β).
Proof.
  rewrite /D_tick /APP.
  simpl_me. rewrite get_fun_tick. reflexivity.
Qed.

Lemma D_tick_eq α : D_tick α = D_thunk (NextO α).
Proof. reflexivity. Qed.
#[global] Opaque D_thunk D_tick D_nat.

(*** Interpretation *)
Program Definition interp_app {A} `{!Cofe A}:
  (A -n> D) -n> (A -n> D) -n> (A -n> D)
  := λne f1 f2 a, APP (f1 a) (f2 a).
Solve Obligations with solve_proper_ish ; solve_proper.

Program Definition interp_lam {A} `{!Cofe A} :
  (prodO D A -n> D) -n> (A -n> D)
  := λne t1 ta, D_arr $ Next (λne x, t1 (x, ta)).
Solve Obligations with solve_proper_ish ; solve_proper.

Program Definition interp_Y_pre :=
  λne self t, let self' := laterO_ap self (NextO t) in
         get_fun (λne f, D_thunk (laterO_ap f self')) t.
Next Obligation.
  intros self t self' n f1 f2 Hf.
  by repeat f_equiv.
Qed.
Next Obligation. solve_proper_ish; solve_proper. Qed.
Next Obligation.
  intros n self1 self2 Hs t.
  cbn-[laterO_ap]. do 2 f_equiv.
  intro f. cbn-[laterO_ap].
  by repeat f_equiv.
Qed.

Program Definition interp_Y_ish : D -n> D :=
  mmuu interp_Y_pre.

Program Definition interp_Y {A} `{!Cofe A}:
  (A -n> D) -n> (A -n> D)
  := λne f a, interp_Y_ish (f a).
Solve Obligations with repeat solve_proper_ish.

Program Definition interp_succ {A} `{!Cofe A}:
  (A -n> D) -n> (A -n> D)
  := λne f a, SUCC (f a).
Solve Obligations with repeat solve_proper_ish.

Program Definition interp_pred {A} `{!Cofe A}:
  (A -n> D) -n> (A -n> D)
  := λne f a, PRED (f a).
Solve Obligations with repeat solve_proper_ish.


Fixpoint interp_ctx (Γ : ctx) : ofe :=
  match Γ with
  | [] => unitO
  | τ::Γ => prodO D (interp_ctx Γ)
  end.

#[export] Instance interp_ctx_cofe Γ : Cofe (interp_ctx Γ).
Proof.
  induction Γ; simpl; apply _.
Qed.

#[export] Instance interp_ctx_inhab Γ : Inhabited (interp_ctx Γ).
Proof.
  induction Γ; simpl; apply _.
Defined.

Equations interp_var {Γ : ctx} {τ : ty} (v : var Γ τ) : interp_ctx Γ → D :=
interp_var (Γ:=(τ::_))     Vz D := fst D;
interp_var (Γ:=(_::Γ)) (Vs v) D := interp_var v (snd D).

#[export]  Instance interp_var_ne Γ (τ : ty) (v : var Γ τ) : NonExpansive (@interp_var Γ _ v).
Proof.
  intros n D1 D2 HD12. induction v; simp interp_var.
  - by f_equiv.
  - eapply IHv. by f_equiv.
Qed.
Global Instance interp_var_proper Γ (τ : ty) (v : var Γ τ) : Proper ((≡) ==> (≡)) (interp_var v).
Proof. apply ne_proper. apply _. Qed.

Program Definition interp_bot {Γ} : Γ -n> D := λne _, D_err.

Equations interp_tm {Γ : ctx} {τ : ty} (M : tm Γ τ) : interp_ctx Γ -n> D :=
interp_tm (Num n) := λne _, D_nat n;
interp_tm (Var v) := OfeMor (interp_var v);
interp_tm (App f a) := interp_app (interp_tm f) (interp_tm a);
interp_tm (Lam N) := interp_lam (interp_tm N);
interp_tm (Succ M) := interp_succ (interp_tm M);
interp_tm (Pred M) := interp_pred (interp_tm M);
interp_tm (Y M) := interp_Y (interp_tm M).

Equations interp_rens_ctx {Γ D : ctx}
          (E : interp_ctx D) (s : rens Γ D) : interp_ctx Γ :=
  interp_rens_ctx (Γ:=[]) E s := tt : interp_ctx [];
  interp_rens_ctx (Γ:=_::_) E s :=
    (interp_var (hd_ren s) E, interp_rens_ctx E (tl_ren s)).

Equations interp_subs_ctx {Γ D : ctx}
          (E : interp_ctx D) (s : subs Γ D) : interp_ctx Γ :=
  interp_subs_ctx (Γ:=[]) E s := tt : interp_ctx [];
  interp_subs_ctx (Γ:=_::_) E s :=
    (interp_tm (hd_sub s) E, interp_subs_ctx E (tl_sub s)).


Global Instance interp_rens_ctx_proper Γ D :
  Proper ((≡) ==> (≡) ==> (≡)) (@interp_rens_ctx Γ D).
Proof.
  intros E E' HE s1 s2 Hs.
  induction Γ as [|τ' Γ]; simp interp_rens_ctx; auto.
  f_equiv.
  - unfold hd_ren; rewrite Hs.
    by rewrite HE.
  - apply IHΓ. intros ? v. unfold tl_ren; by rewrite Hs.
Qed.
Global Instance interp_subs_ctx_proper Γ D :
  Proper ((≡) ==> (≡) ==> (≡)) (@interp_subs_ctx Γ D).
Proof.
  intros E E' HE s1 s2 Hs.
  induction Γ as [|τ' Γ]; simp interp_subs_ctx; auto.
  f_equiv.
  - unfold hd_sub; by rewrite Hs HE.
  - apply IHΓ. intros ? v. unfold tl_sub; by rewrite Hs.
Qed.



Lemma interp_rens_ctx_tl_ren {Γ D τ} x E (r : rens Γ D) :
  interp_rens_ctx ((x, E) : interp_ctx (τ::D)) (tl_ren (rens_lift r))
                  ≡ interp_rens_ctx E r.
Proof.
  induction Γ as [|τ' Γ]; simp interp_rens_ctx; eauto.
  f_equiv.
  { unfold hd_ren, tl_ren. simp rens_lift interp_var.
    done. }
  { rewrite -IHΓ. f_equiv. clear.
    intros τ2 v. dependent elimination v;
                   unfold hd_ren, tl_ren; simp rens_lift; auto. }
Qed.


Lemma interp_tm_ren {Γ D : ctx} {τ} (M : tm Γ τ) (r : rens Γ D) :
  ∀ (E : interp_ctx D),
    interp_tm (ren_tm M r) E ≡ interp_tm M (interp_rens_ctx E r).
Proof.
  revert D r. induction M=> D r E; simp ren_tm interp_tm ; first done.
  all: try by (simp interp_tm; repeat intro; simpl; f_equiv; eauto).
  - simpl. revert r.
    induction v=>r.
    + simp interp_var interp_rens_ctx. done.
    + simp interp_var interp_rens_ctx. simpl.
      apply (IHv (tl_ren r)).
  - simp interp_tm.
    cbn-[D_thunk  D_arr mmuu get_nat].
    f_equiv. f_equiv.
    intros x. simpl.
    rewrite IHM. f_equiv.
    clear.
    destruct Γ as [|τ' Γ]; first done.
    rewrite interp_rens_ctx_equation_2.
    simp interp_var. f_equiv.
    by rewrite interp_rens_ctx_tl_ren.
  - simp interp_tm.
    cbn-[D_thunk D_arr mmuu get_nat later_ap].
    f_equiv; eauto.
    f_equiv; eauto.
    intros g; simpl. repeat f_equiv. eauto.
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
  - simp interp_tm.
    cbn-[D_thunk D_arr mmuu get_nat].
    f_equiv. f_equiv.
    intros x. simpl.
    rewrite IHM. f_equiv.
    clear.
    destruct Γ as [|τ' Γ]; first done.
    rewrite interp_subs_ctx_equation_2.
    unfold hd_sub. simp subs_lift.
    simp interp_tm interp_var.
    f_equiv; first done.
    by rewrite interp_subs_ctx_tl_sub.
  - simp interp_tm.
    cbn-[D_thunk D_arr mmuu get_nat].
    repeat f_equiv; eauto.
    intros g; simpl.
    repeat f_equiv; eauto.
Qed.

Lemma interp_subs_ctx_id {Γ} (E : interp_ctx Γ) :
  interp_subs_ctx E (@idsub Γ) ≡ E.
Proof.
  induction Γ as [|τ' Γ]; simp interp_subs_ctx.
  { by destruct E. }
  destruct E as [x E].
  unfold hd_sub, idsub. simp interp_tm ; simpl; simp interp_var.
  f_equiv; first eauto.
  trans (interp_subs_ctx ((x, E) : interp_ctx (τ'::Γ)) (tl_sub (subs_lift idsub))).
  { f_equiv. intros ? v. unfold tl_sub.
    reflexivity. }
  rewrite interp_subs_ctx_tl_sub.
  apply IHΓ.
Qed.

Ltac simplify_tm :=
  repeat progress first [ simp interp_tm | unfold subst1
                          | simp subst_tm | simp interp_var ].


(** * Soundness *)
Lemma interp_tm_step_beta {C : ctx} {τ : ty} (M N : tm C τ) k :
  step_beta M k N → interp_tm M ≡ OfeMor (D_tick_n k) ◎ interp_tm N.
Proof.
  induction 1; intro D.
  - simplify_tm. cbn-[D_thunk D_arr mmuu get_nat].
    rewrite get_fun_fun D_tick_eq. cbn-[mmuu get_nat].
    f_equiv.
    rewrite interp_tm_subst.
    repeat f_equiv.
    simp interp_subs_ctx. f_equiv; eauto.
    rewrite -{1}(interp_subs_ctx_id D). f_equiv.
    intros ? x. reflexivity.
  - simplify_tm.
    rewrite {1}/interp_Y.
    unfold interp_Y_ish.
    cbn-[interp_Y_ish D_tick get_fun mmuu interp_app].
    etrans.
    { eapply (mmuu_unfold interp_Y_pre). }
    unfold interp_app.
    cbn-[D_tick mmuu D_thunk].
    f_equiv; eauto. f_equiv.
    intro f. reflexivity.
  - simplify_tm.
    cbn-[get_nat D_err D_arr D_nat D_tick].
    rewrite get_nat_nat. done.
  - simplify_tm.
    cbn-[get_nat D_err D_arr D_nat D_tick].
    rewrite -get_nat_tick_n. f_equiv; eauto.
  - simplify_tm.
    cbn-[get_nat D_err D_arr D_nat D_tick].
    rewrite get_nat_nat. done.
  - simplify_tm.
    cbn-[get_nat D_err D_arr D_nat D_tick].
    rewrite -get_nat_tick_n. f_equiv; eauto.
  - simplify_tm.
    cbn-[get_nat get_fun D_err D_arr D_nat D_tick D_thunk later_ap].
    rewrite -get_fun_tick_n. f_equiv; eauto.
Qed.

Lemma interp_sound {Γ : ctx} {τ : ty} (M N : tm Γ τ) k :
  step_beta_clos M k N → interp_tm M ≡ OfeMor (D_tick_n k) ◎ interp_tm N.
Proof.
  induction 1.
  - intros E. done.
  - intros E; cbn.
    rewrite D_tick_add.
    apply interp_tm_step_beta in H.
    rewrite (H _). cbn. f_equiv. eauto.
Qed.
