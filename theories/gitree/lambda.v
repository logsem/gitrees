(** Core 'computational' operations on itrees: lambda, function application, arithmetic, etc *)
From iris.prelude Require Import options.
From iris.base_logic Require Export base_logic.
From gitrees Require Export prelude gitree.core gitree.subofe.

Section lambda.
  Local Opaque laterO_ap.

  Context {Σ : opsInterp} {A : ofe} `{!Cofe A}.

  Notation IT := (IT Σ A).

  Program Definition IF_ne `{!SubOfe natO A} : IT -n> IT -n> IT -n> IT := λne t t1 t2,
      get_ret (λne n, if Nat.ltb 0 n then t1 else t2) t.
  Next Obligation. repeat intro. by rewrite H. Qed.
  Solve All Obligations with solve_proper_please.

  Definition IF `{!SubOfe natO A} x y z := IF_ne x y z.
  Global Instance IF_Proper `{H : !SubOfe natO A}
    : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (@IF H).
  Proof. rewrite /IF; solve_proper_please. Qed.
  Global Instance IF_NonExp `{H : !SubOfe natO A} : NonExpansive3 (@IF H).
  Proof. rewrite /IF; solve_proper_please. Qed.

  Program Definition IF_last_ne `{!SubOfe natO A} : IT -n> IT -n> IT -n> IT := λne t1 t2 t, IF t t1 t2.
  Solve All Obligations with rewrite /IF; solve_proper_please.
  Definition IF_last `{!SubOfe natO A} x y z := IF_last_ne x y z.
  Global Instance IF_last_Proper `{H : !SubOfe natO A}
    : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (@IF_last H).
  Proof. rewrite /IF_last; solve_proper_please. Qed.
  Global Instance IF_last_NonExp `{H : !SubOfe natO A} : NonExpansive3 (@IF_last H).
  Proof. rewrite /IF_last; solve_proper_please. Qed.

  (** A non-strict application, does not recurse under the effects of the argument *)
  Program Definition APP_ne : IT -n> laterO IT -n> IT := λne f x,
      get_fun (λne f, Tau $ laterO_ap f x) f.
  Solve All Obligations with solve_proper_please.
  Definition APP x y := APP_ne x y.
  Global Instance APP_Proper
    : Proper ((≡) ==> (≡) ==> (≡)) APP.
  Proof. rewrite /APP; solve_proper_please. Qed.
  Global Instance APP_NonExp : NonExpansive2 APP.
  Proof. rewrite /APP; solve_proper_please. Qed.

  Program Definition Ppa_ne : laterO IT -n> IT -n> IT := λne x f, APP f x.
  Solve All Obligations with rewrite /APP; solve_proper_please.
  Definition Ppa x y := Ppa_ne x y.
  Global Instance Ppa_Proper
    : Proper ((≡) ==> (≡) ==> (≡)) Ppa.
  Proof. rewrite /Ppa; solve_proper_please. Qed.
  Global Instance Ppa_NonExp : NonExpansive2 Ppa.
  Proof. rewrite /Ppa; solve_proper_please. Qed.

  (** Strict version of APP *)
  Program Definition APP'_ne : IT -n> IT -n> IT := λne f, get_val (APP_ne f ◎ NextO).
  Solve All Obligations with solve_proper_please.
  Definition APP' x y := APP'_ne x y.
  Global Instance APP'_Proper
    : Proper ((≡) ==> (≡) ==> (≡)) APP'.
  Proof. rewrite /APP'; solve_proper_please. Qed.
  Global Instance APP'_NonExp : NonExpansive2 APP'.
  Proof. rewrite /APP'; solve_proper_please. Qed.

  (** We define the interpretation of NatOp in two stages.
      First, we recurse under ticks and visitors in both arguments, and only then perform the op
   *)
  Program Definition NATOP_ne `{!SubOfe natO A} (f : nat → nat → nat) : IT -n> IT -n> IT := λne t1 t2,
      get_val (λne v2,
        get_val (λne v1,
                   get_ret2 (λne n1 n2, Ret (f n1 n2)) v1 v2) t1) t2.
  Solve All Obligations with solve_proper_please.
  Definition NATOP `{!SubOfe natO A} f x y := NATOP_ne f x y.
  Global Instance NATOP_Proper `{H : !SubOfe natO A} f
    : Proper ((≡) ==> (≡) ==> (≡)) (@NATOP H f).
  Proof. rewrite /NATOP; solve_proper_please. Qed.
  Global Instance NATOP_NonExp `{H : !SubOfe natO A} f : NonExpansive2 (@NATOP H f).
  Proof. rewrite /NATOP; solve_proper_please. Qed.

  (** Sequencing *)
  Program Definition SEQ_ne : IT -n> IT -n> IT := λne α β,
      get_val (constO β) α.
  Solve Obligations with solve_proper_please.
  Definition SEQ x y := SEQ_ne x y.
  Global Instance SEQ_Proper
    : Proper ((≡) ==> (≡) ==> (≡)) SEQ.
  Proof. rewrite /SEQ; solve_proper_please. Qed.
  Global Instance SEQ_NonExp : NonExpansive2 SEQ.
  Proof. rewrite /SEQ; solve_proper_please. Qed.

  Program Definition LET_ne : IT -n> (IT -n> IT) -n> IT := λne x f, get_val f x.
  Solve Obligations with solve_proper.
  Definition LET x y := LET_ne x y.
  Global Instance LET_Proper
    : Proper ((≡) ==> (≡) ==> (≡)) LET.
  Proof. rewrite /LET; intros f g Hfg x y Hxy; solve_proper. Qed.
    Global Instance LET_NonExp : NonExpansive2 LET.
  Proof. rewrite /LET; intros n f g Hfg x y Hxy; solve_proper. Qed.

  Lemma APP_Ret x y : APP (core.Ret x) y ≡ Err RuntimeErr.
  Proof. simpl. by rewrite /APP /APP_ne //= core.get_fun_ret. Qed.
  Lemma APP_Err e x : APP (Err e) x ≡ Err e.
  Proof. simpl. by rewrite /APP /APP_ne //= get_fun_err. Qed.
  Lemma APP_Fun f x : APP (Fun f) x ≡ Tau $ laterO_ap f x.
  Proof. simpl. by rewrite /APP /APP_ne //= get_fun_fun. Qed.
  Lemma APP_Tick t x : APP (Tick t) x ≡ Tick $ APP t x.
  Proof.
     rewrite {1}/APP /=.
     by rewrite get_fun_tick.
  Qed.
  Lemma APP_Tick_n n t x : APP (Tick_n n t) x ≡ Tick_n n $ APP t x.
  Proof.
    induction n; eauto. rewrite APP_Tick. rewrite IHn. done.
  Qed.
  Lemma APP_Vis op i k x : APP (Vis op i k) x ≡ Vis op i (laterO_map (Ppa_ne x) ◎ k).
  Proof.
    rewrite {1}/APP /=.
    rewrite get_fun_vis. repeat f_equiv.
    intro f. simpl. reflexivity.
  Qed.
  Lemma APP'_Err_r f e : APP' f (Err e) ≡ Err e.
  Proof. simpl. by rewrite /APP' /APP'_ne //= get_val_err. Qed.
  Lemma APP'_Ret_r f x : APP' f (core.Ret x) ≡ APP f (Next (core.Ret x)).
  Proof. simpl. by rewrite /APP' /APP'_ne //= core.get_val_ret. Qed.
  Lemma APP'_Fun_r f x : APP' f (Fun x) ≡ APP f (Next (Fun x)).
  Proof. simpl. by rewrite /APP' /APP'_ne //= get_val_fun. Qed.
  Lemma APP'_Tick_r f t : APP' f (Tick t) ≡ Tick $ APP' f t.
  Proof. by rewrite /APP' /APP'_ne //= get_val_tick. Qed.
  Lemma APP'_Tick_r_n  f n t : APP' f (Tick_n n t) ≡ Tick_n n $ APP' f t.
  Proof.
    induction n; eauto. by rewrite APP'_Tick_r IHn.
  Qed.
  Lemma APP'_Vis_r f op i k : APP' f (Vis op i k) ≡ Vis op i (laterO_map (APP' f) ◎ k).
  Proof. by rewrite /APP' /APP'_ne //= get_val_vis. Qed.
  Lemma APP_APP'_ITV' α (βv : ITV Σ A) :
    APP' α (IT_of_V βv) ≡ APP α (Next (IT_of_V βv)).
  Proof.
    destruct βv as [n|f]; simpl.
    - rewrite APP'_Ret_r//.
    - rewrite APP'_Fun_r//.
  Qed.
  (* XXX: the names here are weird *)
  Lemma APP_APP'_ITV α β :
    AsVal β → APP' α β ≡ APP α (Next β).
  Proof.
    intros [βv <-].
    rewrite APP_APP'_ITV'//.
  Qed.
  Lemma APP'_Vis_l β op i k `{!AsVal β} :
    APP' (Vis op i k) β ≡ Vis op i (laterO_map (flipO APP'_ne β) ◎ k).
  Proof.
    rewrite APP_APP'_ITV.
    rewrite APP_Vis. repeat f_equiv.
    intro α. cbn-[APP]. by rewrite -APP_APP'_ITV.
  Qed.
  Lemma APP'_Tick_l α β `{!AsVal β} : APP' (Tick α) β ≡ Tick $ APP' α β.
  Proof. rewrite !APP_APP'_ITV. by rewrite APP_Tick. Qed.
  Lemma APP'_Tick_l_n α n β `{!AsVal β} : APP' (Tick_n n α) β ≡ Tick_n n $ APP' α β.
  Proof.
    induction n; eauto. by rewrite APP'_Tick_l IHn.
  Qed.
  Lemma APP'_Err_l e x `{!AsVal x}: APP' (Err e) x ≡ Err e.
  Proof. rewrite APP_APP'_ITV. by rewrite APP_Err. Qed.
  Lemma APP'_Ret_l x t `{!AsVal t}: APP' (core.Ret x) t ≡ Err RuntimeErr.
  Proof. rewrite APP_APP'_ITV. by rewrite APP_Ret. Qed.
  Lemma APP'_Fun_l f x `{!AsVal x} : APP' (Fun f) x ≡ Tau $ laterO_ap f (Next x).
  Proof. rewrite APP_APP'_ITV. by rewrite APP_Fun. Qed.

  Lemma IF_Err `{!SubOfe natO A} e t1 t2 : IF (Err e) t1 t2 ≡ Err e.
  Proof. unfold IF. simpl. by rewrite get_ret_err. Qed.
  Lemma IF_True `{!SubOfe natO A} n t1 t2 :
    0 < n → IF (Ret n) t1 t2 ≡ t1.
  Proof.
    intro Hn. unfold IF. simpl.
    rewrite get_ret_ret.
    destruct n; first lia; last eauto.
  Qed.
  Lemma IF_False `{!SubOfe natO A} n t1 t2 :
    0 ≥ n → IF (Ret n) t1 t2 ≡ t2.
  Proof.
    intro Hn. unfold IF. simpl.
    rewrite get_ret_ret.
    destruct n; first eauto; last lia.
  Qed.
  Lemma IF_Tick `{!SubOfe natO A} t t1 t2 :
    IF (Tick t) t1 t2 ≡ Tick (IF t t1 t2).
  Proof. rewrite {1}/IF /=. apply get_ret_tick. Qed.
  Lemma IF_Tick_n `{!SubOfe natO A} n t t1 t2 :
    IF (Tick_n n t) t1 t2 ≡ Tick_n n (IF t t1 t2).
  Proof.
    induction n; eauto. by rewrite IF_Tick IHn.
  Qed.
  Lemma IF_Vis `{!SubOfe natO A} op i k t1 t2 :
    IF (Vis op i k) t1 t2 ≡ Vis op i (laterO_map (IF_last_ne t1 t2) ◎ k).
  Proof.
    rewrite {1}/IF /=.
    rewrite get_ret_vis. repeat f_equiv.
    by intro.
  Qed.

  Lemma NATOP_Err_r `{!SubOfe natO A} f e t1 : NATOP f t1 (Err e) ≡ Err e.
  Proof. simpl. by rewrite /NATOP /NATOP_ne //= get_val_err. Qed.
  Lemma NATOP_Err_l `{!SubOfe natO A} f e β : AsVal β → NATOP f (Err e) β ≡ Err e.
  Proof.
    intros ?. simpl.
    rewrite /NATOP /NATOP_ne //= get_val_ITV /= get_val_err //.
  Qed.
  Lemma NATOP_Ret `{!SubOfe natO A} n1 n2 f :
    NATOP f (Ret n1) (Ret n2) ≡ Ret (f n1 n2).
  Proof.
    simpl.
    rewrite /NATOP /NATOP_ne /= get_val_ret/= get_val_ret/=.
    rewrite !get_ret_ret. simpl.
    rewrite !get_ret_ret. simpl.
    done.
  Qed.
  Lemma NATOP_Tick_r `{!SubOfe natO A} t1 t2 f :
    NATOP f t1 (Tick t2) ≡ Tick $ NATOP f t1 t2.
  Proof.
    simpl. rewrite /NATOP /NATOP_ne /= get_val_tick//.
  Qed.
  Lemma NATOP_Tick_n_r `{!SubOfe natO A} t1 t2 f n :
    NATOP f t1 (Tick_n n t2) ≡ Tick_n n $ NATOP f t1 t2.
  Proof.
    induction n; eauto. rewrite NATOP_Tick_r.
    rewrite IHn. done.
  Qed.
  Lemma NATOP_ITV_Tick_l `{!SubOfe natO A} t1 β f :
    AsVal β →
    NATOP f (Tick t1) β ≡ Tick $ NATOP f t1 β.
  Proof.
    intros ?. simpl. rewrite /NATOP /NATOP_ne /= get_val_ITV/=.
    rewrite get_val_tick. f_equiv.
    rewrite get_val_ITV. done.
  Qed.
  Lemma NATOP_ITV_Tick_n_l `{!SubOfe natO A} t1 β f n :
    AsVal β →
    NATOP f (Tick_n n t1) β ≡ Tick_n n $ NATOP f t1 β.
  Proof.
    intros Hb.
    induction n; eauto. rewrite NATOP_ITV_Tick_l.
    rewrite IHn. done.
  Qed.
  Lemma NATOP_Vis_r `{!SubOfe natO A} t1 op i k f :
    NATOP f t1 (Vis op i k) ≡ Vis op i (laterO_map (NATOP_ne f t1) ◎ k).
  Proof.
    simpl. rewrite /NATOP /NATOP_ne /= get_val_vis. f_equiv. solve_proper.
  Qed.
  Lemma NATOP_ITV_Vis_l `{!SubOfe natO A} op i k β f :
    AsVal β →
    NATOP f (Vis op i k) β ≡
    Vis op i (laterO_map (flipO (NATOP_ne f) β) ◎ k).
  Proof.
    intros ?. simpl. rewrite /NATOP /NATOP_ne /= get_val_ITV/=.
    rewrite get_val_vis. repeat f_equiv.
    intro y. simpl. rewrite get_val_ITV//.
  Qed.

  Lemma SEQ_Val α β `{!AsVal α} : SEQ α β ≡ β.
  Proof. unfold SEQ. simpl. rewrite get_val_ITV//. Qed.
  Lemma LET_Val α f `{!AsVal α} : LET α f ≡ f α.
  Proof. unfold LET. simpl. rewrite get_val_ITV//. Qed.

  Opaque APP APP' IF NATOP.
  Definition AppLSCtx (β α : IT) := APP' α β.
  Definition AppRSCtx (β α : IT) := APP' β α.
  Definition NatOpLSCtx `{!SubOfe natO A} f (β α : IT) := NATOP f α β.
  Definition NatOpRSCtx `{!SubOfe natO A} f (β α : IT) := NATOP f β α.
  Definition IFSCtx `{!SubOfe natO A} (β1 β2 α : IT) := IF α β1 β2.
  Definition SEQCtx (β2 α : IT) := SEQ α β2.
  Definition LETCTX f : IT -n> IT := λne x, LET x f.

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
    - intros e. by rewrite !APP_APP'_ITV APP_Err.
  Qed.
  #[export] Instance AppRSCtx_hom (β : IT) : IT_hom (AppRSCtx β) | 0.
  Proof.
    unfold AppRSCtx.
    simple refine (IT_HOM _ _ _ _ _); simpl.
    - solve_proper.
    - intros a. by rewrite APP'_Tick_r.
    - intros op i k. rewrite APP'_Vis_r. repeat f_equiv.
      by intro.
    - intros e. by rewrite APP'_Err_r.
  Qed.
  #[local] Instance NatOpLSCtx_ne op (β : IT) `{!SubOfe natO A} : NonExpansive (NatOpLSCtx op β).
  Proof.
    intro n. unfold NatOpLSCtx.
    repeat intro. repeat f_equiv; eauto.
  Qed.
  #[export] Instance NatOpLSCtx_hom op (β : IT) `{!SubOfe natO A} `{!AsVal β} : IT_hom (NatOpLSCtx op β).
  Proof.
    unfold NatOpLSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite NATOP_ITV_Tick_l//.
    - intros op' i k. simpl. rewrite NATOP_ITV_Vis_l//.
      repeat f_equiv. intro. reflexivity.
    - intros e. simpl. rewrite NATOP_Err_l//.
  Qed.
  #[local] Instance NatOpRSCtx_ne op (β : IT) `{!SubOfe natO A} : NonExpansive (NatOpRSCtx op β).
  Proof.
    intro n. unfold NatOpRSCtx.
    solve_proper.
  Qed.
  #[export] Instance NatOpRSCtx_hom op (β : IT) `{!SubOfe natO A} : IT_hom (NatOpRSCtx op β).
  Proof.
    unfold NatOpRSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite NATOP_Tick_r//.
    - intros op' i k. simpl. rewrite NATOP_Vis_r//.
      repeat f_equiv. intro. reflexivity.
    - intros e. simpl. rewrite NATOP_Err_r//.
  Qed.
  #[local] Instance IFSCtx_ne (β1 β2 : IT) `{!SubOfe natO A} : NonExpansive (IFSCtx β1 β2).
  Proof. unfold IFSCtx. solve_proper. Qed.
  #[export] Instance IFSCtx_hom (β1 β2 : IT) `{!SubOfe natO A} : IT_hom (IFSCtx β1 β2).
  Proof.
    unfold IFSCtx.
    simple refine (IT_HOM _ _ _ _ _).
    - intro a. simpl. rewrite IF_Tick//.
    - intros op i k. simpl. rewrite IF_Vis.
      repeat f_equiv. intro α. reflexivity.
    - intros e. simpl. rewrite IF_Err//.
  Qed.
  Instance SEQCtx_ne β2 : NonExpansive (SEQCtx β2).
  Proof. solve_proper. Qed.
  #[export] Instance SEQ_hom (β2 : IT) : IT_hom (SEQCtx β2).
  Proof.
    unfold SEQCtx. unfold SEQ.
    simpl. apply _.
  Qed.
  #[export] Instance LETCTX_Hom f : IT_hom (LETCTX f).
  Proof.
    unfold LETCTX, LET.
    simpl. apply get_val_hom.
  Qed.

End lambda.

#[global] Opaque APP APP' IF NATOP SEQ LET.

Notation "'λit' x .. y , P" := (Fun (Next (λne x, .. (Fun (Next (λne y, P))) .. )))
  (at level 200, x binder, y binder, right associativity,
    format "λit  x  ..  y ,  P").

Notation "f ⊙ x" := (APP' f x)
                      (at level 10,  left associativity).
