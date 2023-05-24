(** Core 'computational' operations on itrees: lambda, function application, arithmetic, etc *)
From iris.prelude Require Import options.
From iris.base_logic Require Export base_logic.
From gitrees Require Import prelude gitree.core.

Section lambda.
  Local Opaque laterO_ap.

  Context {Σ : opsInterp}.
  Notation IT := (IT Σ).

  Program Definition IF : IT -n> IT -n> IT -n> IT := λne t t1 t2,
      get_nat (λne n, if Nat.ltb 0 n then t1 else t2) t.
  Next Obligation.
    intros _ t1 t2 n x y ->. done.
  Qed.
  Solve All Obligations with solve_proper.

  Program Definition IF_last : IT -n> IT -n> IT -n> IT := λne t1 t2 t, IF t t1 t2.
  Solve All Obligations with solve_proper.


  (** A non-strict application, does not recurse under the effects of the argument *)
  Program Definition APP : IT -n> laterO IT -n> IT := λne f x,
    get_fun (λne f, Tau $ laterO_ap f x) f.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    repeat intro. repeat f_equiv. intro. solve_proper.
  Qed.
  Next Obligation.
    repeat intro. repeat f_equiv.
    repeat intro. solve_proper.
  Qed.
  Program Definition Ppa : laterO IT -n> IT -n> IT := λne x f, APP f x.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    repeat intro. repeat f_equiv. repeat intro. simpl.
    repeat f_equiv. intro. solve_proper.
  Qed.

  (** Strict version of APP *)
  Program Definition APP' : IT -n> IT -n> IT := λne f, get_val (APP f ◎ NextO).
  Next Obligation. repeat intro; by repeat f_equiv. Qed.

  (** We define the interpretation of NatOp in two stages.
      First, we recurse under ticks and visitors in both arguments, and only then perform the op
   *)
  Program Definition NATOP (f : nat → nat → nat) : IT -n> IT -n> IT := λne t1 t2,
      get_val (λne v2,
        get_val (λne v1,
                   get_nat2 (λ n1 n2, Nat (f n1 n2)) v1 v2) t1) t2.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    repeat intro. repeat f_equiv. solve_proper.
  Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    repeat intro. simpl. repeat f_equiv.
    intro. simpl. solve_proper.
  Qed.

  Lemma APP_Err x : APP Err x ≡ Err.
  Proof. simpl. by rewrite get_fun_err. Qed.
  Lemma APP_Fun f x : APP (Fun f) x ≡ Tau $ laterO_ap f x.
  Proof. simpl. rewrite get_fun_fun. done. Qed.
  Lemma APP_Tick t x : APP (Tick t) x ≡ Tick $ APP t x.
  Proof.
     rewrite {1}/APP /=.
     by rewrite get_fun_tick.
  Qed.
  Lemma APP_Tick_n n t x : APP (Tick_n n t) x ≡ Tick_n n $ APP t x.
  Proof.
    induction n; eauto. rewrite APP_Tick. rewrite IHn. done.
  Qed.
  Lemma APP_Vis op i k x : APP (Vis op i k) x ≡ Vis op i (laterO_map (Ppa x) ◎ k).
  Proof.
    rewrite {1}/APP /=.
    rewrite get_fun_vis. repeat f_equiv.
    intro f. simpl. reflexivity.
  Qed.
  Lemma APP'_Err f : APP' f Err ≡ Err.
  Proof. simpl. by rewrite get_val_err. Qed.
  Lemma APP'_Nat f x : APP' f (Nat x) ≡ APP f (Next (Nat x)).
  Proof. simpl. rewrite get_val_nat. done. Qed.
  Lemma APP'_Fun f x : APP' f (Fun x) ≡ APP f (Next (Fun x)).
  Proof. simpl. rewrite get_val_fun. done. Qed.
  Lemma APP'_Tick_r f t : APP' f (Tick t) ≡ Tick $ APP' f t.
  Proof. by rewrite get_val_tick. Qed.
  Lemma APP'_Tick_r_n  f n t : APP' f (Tick_n n t) ≡ Tick_n n $ APP' f t.
  Proof.
    induction n; eauto. by rewrite APP'_Tick_r IHn.
  Qed.
  Lemma APP'_Vis_r f op i k : APP' f (Vis op i k) ≡ Vis op i (laterO_map (APP' f) ◎ k).
  Proof. by rewrite get_val_vis. Qed.
  Lemma APP_APP'_ITV' α (βv : ITV Σ) :
    APP' α (IT_of_V βv) ≡ APP α (Next (IT_of_V βv)).
  Proof.
    destruct βv as [n|f]; simpl.
    - rewrite APP'_Nat//.
    - rewrite APP'_Fun//.
  Qed.
  (* XXX: the names here are weird *)
  Lemma APP_APP'_ITV α β :
    AsVal β → APP' α β ≡ APP α (Next β).
  Proof.
    intros [βv <-].
    rewrite APP_APP'_ITV'//.
  Qed.

  Lemma IF_Err t1 t2 : IF Err t1 t2 ≡ Err.
  Proof. unfold IF. simpl. by rewrite get_nat_err. Qed.
  Lemma IF_True n t1 t2 :
    0 < n → IF (Nat n) t1 t2 ≡ t1.
  Proof.
    intro Hn. unfold IF. simpl.
    rewrite get_nat_nat.
    assert (0 <? n = true) as ->; last by eauto.
    by apply Nat.ltb_lt.
  Qed.
  Lemma IF_False n t1 t2 :
    0 ≥ n → IF (Nat n) t1 t2 ≡ t2.
  Proof.
    intro Hn. unfold IF. simpl.
    rewrite get_nat_nat.
    assert (0 <? n = false) as ->; last by eauto.
    by apply Nat.ltb_ge.
  Qed.
  Lemma IF_Tick t t1 t2 :
    IF (Tick t) t1 t2 ≡ Tick (IF t t1 t2).
  Proof. rewrite {1}/IF /=. apply get_nat_tick. Qed.
  Lemma IF_Tick_n n t t1 t2 :
    IF (Tick_n n t) t1 t2 ≡ Tick_n n (IF t t1 t2).
  Proof.
    induction n; eauto. by rewrite IF_Tick IHn.
  Qed.
  Lemma IF_Vis op i k t1 t2 :
    IF (Vis op i k) t1 t2 ≡ Vis op i (laterO_map (IF_last t1 t2) ◎ k).
  Proof.
    rewrite {1}/IF /=.
    rewrite get_nat_vis. repeat f_equiv.
    by intro.
  Qed.

  Lemma NATOP_Err_r f t1 : NATOP f t1 Err ≡ Err.
  Proof. simpl. by rewrite get_val_err. Qed.
  Lemma NATOP_Err_l f β : AsVal β → NATOP f Err β ≡ Err.
  Proof.
    intros ?. simpl.
    rewrite get_val_ITV /= get_val_err //.
  Qed.
  Lemma NATOP_Nat n1 n2 f :
    NATOP f (Nat n1) (Nat n2) ≡ Nat (f n1 n2).
  Proof.
    simpl.
    rewrite get_val_nat/= get_val_nat/=.
    Transparent get_nat2.
    rewrite /get_nat2/=.
    by rewrite !get_nat_nat.
    Opaque get_nat2.
  Qed.
  Lemma NATOP_Tick_r t1 t2 f :
    NATOP f t1 (Tick t2) ≡ Tick $ NATOP f t1 t2.
  Proof.
    simpl. rewrite get_val_tick//.
  Qed.
  Lemma NATOP_Tick_n_r t1 t2 f n :
    NATOP f t1 (Tick_n n t2) ≡ Tick_n n $ NATOP f t1 t2.
  Proof.
    induction n; eauto. rewrite NATOP_Tick_r.
    rewrite IHn. done.
  Qed.
  Lemma NATOP_ITV_Tick_l t1 β f :
    AsVal β →
    NATOP f (Tick t1) β ≡ Tick $ NATOP f t1 β.
  Proof.
    intros ?. simpl. rewrite get_val_ITV/=.
    rewrite get_val_tick. f_equiv.
    rewrite get_val_ITV. done.
  Qed.
  Lemma NATOP_ITV_Tick_n_l t1 β f n :
    AsVal β →
    NATOP f (Tick_n n t1) β ≡ Tick_n n $ NATOP f t1 β.
  Proof.
    intros Hb.
    induction n; eauto. rewrite NATOP_ITV_Tick_l.
    rewrite IHn. done.
  Qed.
  Lemma NATOP_Vis_r t1 op i k f :
    NATOP f t1 (Vis op i k) ≡ Vis op i (laterO_map (NATOP f t1) ◎ k).
  Proof.
    simpl. rewrite get_val_vis. f_equiv. solve_proper.
  Qed.
  Lemma NATOP_ITV_Vis_l op i k β f :
    AsVal β →
    NATOP f (Vis op i k) β ≡
    Vis op i (laterO_map (flipO (NATOP f) β) ◎ k).
  Proof.
    intros ?. simpl. rewrite get_val_ITV/=.
    rewrite get_val_vis. repeat f_equiv.
    intro y. simpl. rewrite get_val_ITV//.
  Qed.

  Global Instance IF_Proper : Proper ((≡) ==> (≡)) IF.
  Proof. apply ne_proper. apply _. Qed.
  Global Instance APP_Proper : Proper ((≡) ==> (≡)) APP.
  Proof. apply ne_proper. apply _. Qed.
  Global Instance APP'_Proper : Proper ((≡) ==> (≡)) APP'.
  Proof. apply ne_proper. apply _. Qed.
  Global Instance NATOP_Proper f : Proper ((≡) ==> (≡)) (NATOP f).
  Proof. apply ne_proper. apply _. Qed.
  (* XXX!!! *)
  (* Global Instance APP_Proper : Proper ((≡) ==> (≡) ==> (≡)) APP. *)

  Opaque APP APP' IF NATOP.
  Definition AppLSCtx (β α : IT) := APP' α β.
  Definition AppRSCtx (β α : IT) := APP' β α.
  Definition NatOpLSCtx f (β α : IT) := NATOP f α β.
  Definition NatOpRSCtx f (β α : IT) := NATOP f β α.
  Definition IFSCtx (β1 β2 α : IT) := IF α β1 β2.

  #[export] Instance AppLSCtx_hom (β : IT) : AsVal β → IT_hom (AppLSCtx β) | 0.
  Proof.
    intros Hb. unfold AppLSCtx.
    simple refine (IT_HOM _ _ _ _ _); simpl.
    - solve_proper.
    - intros a. rewrite !APP_APP'_ITV.
      by rewrite APP_Tick.
    - intros op i k. rewrite !APP_APP'_ITV.
      rewrite APP_Vis. repeat f_equiv.
      intro x ; simpl. by rewrite APP_APP'_ITV.
    - by rewrite !APP_APP'_ITV APP_Err.
  Qed.
  #[export] Instance AppRSCtx_hom (β : IT) : IT_hom (AppRSCtx β) | 0.
  Proof.
    unfold AppRSCtx.
    simple refine (IT_HOM _ _ _ _ _); simpl.
    - solve_proper.
    - intros a. by rewrite APP'_Tick_r.
    - intros op i k. rewrite APP'_Vis_r. repeat f_equiv.
    - by rewrite APP'_Err.
  Qed.
  #[local] Instance NatOpLSCtx_ne op (β : IT) : NonExpansive (NatOpLSCtx op β).
  Proof.
    intro n. unfold NatOpLSCtx.
    repeat intro. repeat f_equiv; eauto.
  Qed.
  #[export] Instance NatOpLSCtx_hom op (β : IT) : AsVal β → IT_hom (NatOpLSCtx op β).
  Proof.
    intros Hb. unfold NatOpLSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite NATOP_ITV_Tick_l//.
    - intros op' i k. simpl. rewrite NATOP_ITV_Vis_l//.
      repeat f_equiv. intro. reflexivity.
    - simpl. rewrite NATOP_Err_l//.
  Qed.
  #[local] Instance NatOpRSCtx_ne op (β : IT) : NonExpansive (NatOpRSCtx op β).
  Proof.
    intro n. unfold NatOpRSCtx.
    repeat intro. by apply (NATOP _ β).
    (* XXX why doesn't f_equiv work here? *)
  Qed.
  #[export] Instance NatOpRSCtx_hom op (β : IT) : IT_hom (NatOpRSCtx op β).
  Proof.
    unfold NatOpRSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite NATOP_Tick_r//.
    - intros op' i k. simpl. rewrite NATOP_Vis_r//.
      repeat f_equiv. intro. reflexivity.
    - simpl. rewrite NATOP_Err_r//.
  Qed.
  #[local] Instance IFSCtx_ne (β1 β2 : IT) : NonExpansive (IFSCtx β1 β2).
  Proof. unfold IFSCtx. solve_proper. Qed.
  #[export] Instance IFSCtx_hom (β1 β2 : IT) : IT_hom (IFSCtx β1 β2).
  Proof.
    unfold IFSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite IF_Tick//.
    - intros op i k. simpl. rewrite IF_Vis.
      repeat f_equiv. intro α. reflexivity.
    - simpl. rewrite IF_Err//.
  Qed.

End lambda.

#[global] Opaque APP APP' IF NATOP.
