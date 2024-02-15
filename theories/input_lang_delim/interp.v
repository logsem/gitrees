(* From Equations Require Import Equations. *)
From gitrees Require Import gitree.
From gitrees.input_lang_delim Require Import lang.
Require Import gitrees.lang_generic_sem.
From iris.algebra Require Import gmap excl auth gmap_view.
From iris.proofmode Require Import classes tactics.
From iris.base_logic Require Import algebra.
From iris.heap_lang Require Export locations.

Require Import Binding.Lib.
Require Import Binding.Set.


(** * State *)

(* Definition stateF : oFunctor := (gmapOF unitO (▶ ∙))%OF. *)

(* #[local] Instance state_inhabited : Inhabited (stateF ♯ unitO). *)
(* Proof. apply _. Qed. *)
(* #[local] Instance state_cofe X `{!Cofe X} : Cofe (stateF ♯ X). *)
(* Proof. apply _. Qed. *)

Definition stateF : oFunctor := (listOF (▶ ∙ -n> ▶ ∙))%OF.

#[local] Instance state_inhabited : Inhabited (stateF ♯ unitO).
Proof. apply _. Qed.

#[local] Instance state_cofe X `{!Cofe X} : Cofe (stateF ♯ X).
Proof. apply _. Qed.

(* We store a list of meta continuations in the state. *)


(** * Signatures *)

Program Definition shiftE : opInterp :=
  {|
    Ins := ((▶ ∙ -n> ▶ ∙) -n> ▶ ∙);
    Outs := (▶ ∙);
  |}.

Program Definition resetE : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := (▶ ∙);
  |}.

(* to apply the head of the meta continuation *)
Program Definition metaE : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := (▶ ∙);
  |}.


Definition delimE := @[shiftE; resetE; metaE].



Notation op_shift := (inl ()).
Notation op_reset := (inr (inl ())).
Notation op_meta := (inr (inr (inl ()))).



Section reifiers.

  Context {X} `{!Cofe X}.
  Notation state := (stateF ♯ X).


  Definition reify_shift : ((laterO X -n> laterO X) -n> laterO X) *
                              state * (laterO X -n> laterO X) →
                            option (laterO X * state) :=
    λ '(f, σ, k), Some ((f k): laterO X, σ : state).
  #[export] Instance reify_shift_ne :
    NonExpansive (reify_shift :
      prodO (prodO ((laterO X -n> laterO X) -n> laterO X) state)
        (laterO X -n> laterO X) →
      optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. repeat f_equiv; auto. Qed.

  Definition reify_reset : (laterO X) * state * (laterO X -n> laterO X) →
                           option (laterO X * state) :=
    λ '(e, σ, k), Some (e, (k :: σ)).
  #[export] Instance reify_reset_ne :
    NonExpansive (reify_reset :
        prodO (prodO (laterO X) state) (laterO X -n> laterO X) →
        optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. by repeat f_equiv. Qed.


  Definition reify_meta : (laterO X) * state * (laterO X -n> laterO X) →
                           option (laterO X * state) :=
    λ '(e, σ, k),
      match σ with
      | [] => Some (e, σ)
      | k' :: σ' => Some (k' e, σ')
      end.
  #[export] Instance reify_meta_ne :
    NonExpansive (reify_meta :
        prodO (prodO (laterO X) state) (laterO X -n> laterO X) →
        optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. by repeat f_equiv. Qed.


End reifiers.

Canonical Structure reify_delim : sReifier.
Proof.
  simple refine {|
             sReifier_ops := delimE;
             sReifier_state := stateF
           |}.
  intros X HX op.
  destruct op as [ | [ | [ | []]]]; simpl.
  - simple refine (OfeMor (reify_shift)).
  - simple refine (OfeMor (reify_reset)).
  - simple refine (OfeMor (reify_meta)).
Defined.



Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff delimE E}.
  Context {subOfe0 : SubOfe natO A}.
  Context {subOfe1 : SubOfe unitO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).




  Program Definition SHIFT_ : ((laterO IT -n> laterO IT) -n> laterO IT) -n>
                                (laterO IT -n> laterO IT) -n>
                                IT :=
    λne f k, Vis (E:=E) (subEff_opid op_shift)
             (subEff_ins (F:=delimE) (op:=op_shift) f)
             (k ◎ (subEff_outs (F:=delimE) (op:=op_shift))^-1).
  Solve All Obligations with solve_proper.

  Program Definition SHIFT : ((laterO IT -n> laterO IT) -n> laterO IT) -n> IT :=
    λne f, SHIFT_ f (idfun).
  Solve Obligations with solve_proper.

  Lemma hom_SHIFT_ k e f `{!IT_hom f} :
    f (SHIFT_ e k) ≡ SHIFT_ e (laterO_map (OfeMor f) ◎ k).
  Proof.
    unfold SHIFT_.
    rewrite hom_vis/=.
    f_equiv. by intro.
  Qed.


  Program Definition META : IT -n> IT :=
    λne e, Vis (E:=E) (subEff_opid op_meta)
             (subEff_ins (F:=delimE) (op:=op_meta) (Next e))
             ((subEff_outs (F:=delimE) (op:=op_meta))^-1).
  Solve All Obligations with solve_proper.

  Program Definition RESET_ : (laterO IT -n> laterO IT) -n>
                                laterO IT -n>
                                IT :=
    λne k e, Vis (E:=E) (subEff_opid op_reset)
               (subEff_ins (F := delimE) (op := op_reset) (laterO_map (get_val META) e))
               (k ◎ subEff_outs (F := delimE) (op := op_reset)^-1).
  Solve Obligations with solve_proper.

  Program Definition RESET : laterO IT -n> IT :=
    RESET_ idfun.



End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_delim rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation state := (stateF ♯ IT).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  (** * The symbolic execution rules *)


  (** ** SHIFT *)

  Lemma wp_shift (σ : state) (f : (laterO IT -n> laterO IT) -n> laterO IT)
    (k : IT -n> IT) {Hk : IT_hom k} Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} idfun (later_car (f (laterO_map k))) @ s {{ Φ }}) -∗
    WP@{rs} (k (SHIFT f)) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold SHIFT. simpl.
    rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ (later_map idfun $ f (laterO_map k)) with "Hs").
    {
      simpl.
      repeat f_equiv.
      - rewrite ccompose_id_l later_map_id.
        f_equiv. intro. simpl. by rewrite ofe_iso_21.
      - reflexivity.
    }
    { by rewrite later_map_Next. }
    iModIntro.
    iApply "Ha".
  Qed.



  Lemma wp_reset (σ : state) (e : laterO IT) (k : IT -n> IT) {Hk : IT_hom k}
    Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗
       WP@{rs} get_val META (later_car e) @ s {{ Φ }}) -∗
    WP@{rs} k $ (RESET e) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold RESET. simpl. rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ (laterO_map (get_val META) e) with "Hs").
    - simpl. repeat f_equiv. rewrite ccompose_id_l.
      trans ((laterO_map k) :: σ); last reflexivity.
      f_equiv. intro. simpl. by rewrite ofe_iso_21.
    - reflexivity.
    - iApply "Ha".
  Qed.


  Lemma wp_meta_end (v : ITV) (k : IT -n> IT) {Hk : IT_hom k}
    Φ s :
    has_substate [] -∗
    ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} IT_of_V v @ s {{ Φ }}) -∗
    WP@{rs} k $ get_val META (IT_of_V v) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl. rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ ((Next $ IT_of_V v)) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_meta_cons (σ : state) (v : ITV) (k : IT -n> IT) {Hk : IT_hom k}
    Φ s :
    has_substate ((laterO_map k) :: σ) -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k $ IT_of_V v @ s {{ Φ }}) -∗
    WP@{rs} k $ get_val META (IT_of_V v) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl. rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ ((laterO_map k (Next $ IT_of_V v))) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

End weakestpre.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  Context {subR : subReifier reify_delim rs}.
  Context {R} `{CR : !Cofe R}.
  Context `{!SubOfe natO R}.
  Context `{!SubOfe unitO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Notation state := (stateF ♯ IT).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Global Instance denot_cont_ne (κ : IT -n> IT) :
    NonExpansive (λ x : IT, Tau (laterO_map κ (Next x))).
  Proof.
    solve_proper.
  Qed.

  (** * Interpreting individual operators *)

  (** ** RESET *)

  Program Definition interp_reset {S} (e : S -n> IT) : S -n> IT :=
    λne env, RESET (Next $ e env).
  Solve All Obligations with solve_proper.

  (** ** SHIFT *)

  Program Definition interp_shift {S} (e : @interp_scope F R _ (inc S) -n> IT) :
    interp_scope S -n> IT :=
    λne env, SHIFT (λne (k : laterO IT -n> laterO IT),
                      Next (e (@extend_scope F R _ _ env (λit x, Tau (k (Next x)))))).
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros [| a]; simpl; last solve_proper.
    repeat f_equiv.
    intros ?; simpl.
    by repeat f_equiv.
  Qed.
  Next Obligation.
    solve_proper_prepare.
    repeat f_equiv.
    intros ?; simpl.
    repeat f_equiv.
    intros [| a]; simpl; last solve_proper.
    repeat f_equiv.
  Qed.


  (** ** NATOP *)
  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_natop.


  (** ** REC *)
  Opaque laterO_map.
  Program Definition interp_rec_pre {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT)
    : laterO (@interp_scope F R _ S -n> IT) -n> @interp_scope F R _ S -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : @interp_scope F R  _ S -n> IT) (a : IT),
                      body (@extend_scope F R _ _ (@extend_scope F R _ _ env (self env)) a)) self.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv; intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    do 3 f_equiv; intros ??; simpl; f_equiv;
    intros [| [| y']]; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros.
    solve_proper_prepare.
    by do 2 f_equiv.
  Qed.

  Program Definition interp_rec {S : Set}
    (body : @interp_scope F R _ (inc (inc S)) -n> IT) :
    @interp_scope F R _ S -n> IT :=
    mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set}
    (body : @interp_scope F R _ (inc (inc S)) -n> IT) env : IT -n> IT :=
    λne a, body (@extend_scope F R _ _
                   (@extend_scope F R _ _ env (interp_rec body env))
                   a).
  Next Obligation.
    intros.
    solve_proper_prepare.
    f_equiv. intros [| [| y']]; simpl; solve_proper.
  Qed.

  Lemma interp_rec_unfold {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT) env :
    interp_rec body env ≡ Fun $ Next $ ir_unf body env.
  Proof.
    trans (interp_rec_pre body (Next (interp_rec body)) env).
    { f_equiv. rewrite /interp_rec. apply mmuu_unfold. }
    simpl. rewrite laterO_map_Next. repeat f_equiv.
    simpl. unfold ir_unf. intro. simpl. reflexivity.
  Qed.


  (** ** APP *)
  Program Definition interp_app {A} (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, APP' (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_app_ne A : NonExpansive2 (@interp_app A).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_app.

  (** ** IF *)
  Program Definition interp_if {A} (t0 t1 t2 : A -n> IT) : A -n> IT :=
    λne env, IF (t0 env) (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  (** ** NAT *)
  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Ret n.

  (** ** CONT *)
  Program Definition interp_cont_val {S} (K : S -n> (IT -n> IT)) : S -n> IT :=
    λne env, (λit x, Tau (laterO_map (K env) (Next x))).
  Solve All Obligations with solve_proper_please.

  (* Program Definition interp_cont {S} (e : @interp_scope F R _ (inc S) -n> IT) : *)
  (*   interp_scope S -n> IT := *)
  (*   λne env, (Fun (Next (λne x, Tick $ e (@extend_scope F R _ _ env x)))). *)
  (* Next Obligation. *)
  (*   solve_proper_prepare. repeat f_equiv. *)
  (*   intros [|a]; eauto. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   solve_proper_prepare. *)
  (*   repeat f_equiv. *)
  (*   intro. simpl. repeat f_equiv. *)
  (*   intros [|z]; eauto. *)
  (* Qed. *)

  (* #[local] Instance interp_reset_full_ne {S} (f : @interp_scope F R _ S -n> IT): *)
  (*   NonExpansive (λ env, interp_reset (f env)). *)
  (* Proof. solve_proper. Qed. *)

  Program Definition interp_ifk {A} (e1 e2 : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> (IT -n> IT) :=
  λne env b, (K env) $ interp_if (λne env, b) e1 e2 env.
  Solve All Obligations with solve_proper.

  Program Definition interp_apprk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app q (λne env, t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_applk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app (λne env, t) q env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoprk {A} (op : nat_op) (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_natop op q (λne env, t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_natoplk {A} (op : nat_op) (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_natop op (λne env, t) q env.
  Solve All Obligations with solve_proper.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | LitV n => interp_nat n
    | RecV e => interp_rec (interp_expr e)
    | ContV K => interp_cont_val (interp_cont K)
    end
  with
  interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
    match e with
    | Val v => interp_val v
    | Var x => interp_var x
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
    | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
    | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
    | Shift e => interp_shift (interp_expr e)
    | Reset e => interp_reset (interp_expr e)
    end
  with
  interp_cont {S} (K : cont S) : interp_scope S -n> (IT -n> IT) :=
    match K with
    | END => λne env x, x
    | IfK e1 e2 K => interp_ifk (interp_expr e1) (interp_expr e2) (interp_cont K)
    | AppLK v K => interp_applk (interp_val v) (interp_cont K)
    | AppRK e K => interp_apprk (interp_expr e) (interp_cont K)
    | NatOpLK op v K => interp_natoplk op (interp_val v) (interp_cont K)
    | NatOpRK op e K => interp_natoprk op (interp_expr e) (interp_cont K)
    end.

  (** ** Interpretation of configurations *)

  Program Definition map_meta_cont {S} (mk : Mcont S) : @interp_scope F R _ S -n> state :=
    λne env, list_fmap _ _ (λ k, laterO_map (get_val (META) ◎ (interp_cont k env))) mk.
  Next Obligation. intros S mk n ???. apply list_fmap_ext_ne. intro. by repeat f_equiv. Qed.

  Lemma map_meta_cont_cons {S} (k : cont S) (mk : Mcont S) env :
    map_meta_cont (k::mk) env = (laterO_map ((get_val META) ◎ interp_cont k env)) :: (map_meta_cont mk env).
  Proof. done. Qed.

  Program Definition interp_config {S} (C : config S) : @interp_scope F R _  S -n> (prodO IT state) :=
      match C with
      | Cexpr e => λne env, (get_val META (interp_expr e env), []) : prodO IT state
      | Ceval e K mk => λne env, (get_val META (interp_cont K env (interp_expr e env)),
                                    map_meta_cont mk env)
      | Ccont K v mk => λne env, (get_val META (interp_cont K env (interp_val v env)),
                                    map_meta_cont mk env)
      | Cmcont mk v => λne env, (get_val META (interp_val v env),
                                   map_meta_cont mk env)
      | Cret v => λne env, (get_val META (interp_val v env), [])
      end.
  Solve Obligations with try solve_proper.
  Next Obligation.
    intros S C e K mk <- n???. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros S C v K mk <- n???. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros S C v mk <- n???. by repeat f_equiv.
  Qed.


  Global Instance interp_val_asval {S} {D : interp_scope S} (v : val S)
    : AsVal (interp_val v D).
  Proof.
    destruct v; simpl.
    - apply _.
    - rewrite interp_rec_unfold. apply _.
    - apply _.
  Qed.

  Global Instance ArrEquiv {A B : Set} : Equiv (A [→] B) :=
    fun f g => ∀ x, f x = g x.

  Global Instance ArrDist {A B : Set} `{Dist B} : Dist (A [→] B) :=
    fun n => fun f g => ∀ x, f x ≡{n}≡ g x.

  Global Instance ren_scope_proper {S S'} :
    Proper ((≡) ==> (≡) ==> (≡)) (@ren_scope F _ CR S S').
  Proof.
    intros D D' HE s1 s2 Hs.
    intros x; simpl.
    f_equiv.
    - apply Hs.
    - apply HE.
 Qed.

  Lemma interp_expr_ren {S S'} env
    (δ : S [→] S') (e : expr S) :
    interp_expr (fmap δ e) env ≡ interp_expr e (ren_scope δ env)
  with interp_val_ren {S S'} env
         (δ : S [→] S') (e : val S) :
    interp_val (fmap δ e) env ≡ interp_val e (ren_scope δ env)
  with interp_cont_ren {S S'} env
         (δ : S [→] S') (K : cont S) :
    interp_cont (fmap δ K) env ≡ interp_cont K (ren_scope δ env).
  Proof.
    - destruct e; simpl; try by repeat f_equiv.
      + repeat f_equiv. intro; simpl; repeat f_equiv.
        rewrite interp_expr_ren. f_equiv.
        intros [|a]; simpl; last done.
        by repeat f_equiv.
    - destruct e; simpl.
      + reflexivity.
      + clear -interp_expr_ren.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 1 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_ren.
        iApply f_equivI.
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done; last done.
        by iRewrite - "IH".
      + repeat f_equiv.
        intro. simpl. repeat f_equiv.
        apply interp_cont_ren.
    - destruct K; simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_ren || apply interp_val_ren || apply interp_cont_ren).
  Qed.


  (* Lemma interp_ectx_ren {S S'} env (δ : S [→] S') (K : ectx S) : *)
  (*   interp_ectx (fmap δ K) env ≡ interp_ectx K (ren_scope δ env). *)
  (* Proof. *)
  (*   induction K; intros ?; simpl; eauto. *)
  (*   destruct a; simpl; try (etrans; first by apply IHK); repeat f_equiv; *)
  (*      try solve [by apply interp_expr_ren | by apply interp_val_ren]. *)
  (* Qed. *)


  Lemma interp_comp {S} (e : expr S) (env : interp_scope S) (K : cont S):
    interp_expr (fill K e) env ≡ (interp_cont K) env ((interp_expr e) env).
  Proof. elim : K e env; eauto. Qed.

  Program Definition sub_scope {S S'} (δ : S [⇒] S') (env : interp_scope S')
    : interp_scope S := λne x, interp_expr (δ x) env.

  Global Instance SubEquiv {A B : Set} : Equiv (A [⇒] B) := fun f g => ∀ x, f x = g x.

  Global Instance sub_scope_proper {S S'} :
    Proper ((≡) ==> (≡) ==> (≡)) (@sub_scope S S').
  Proof.
    intros D D' HE s1 s2 Hs.
    intros x; simpl.
    f_equiv.
    - f_equiv.
      apply HE.
    - apply Hs.
 Qed.

  Lemma interp_expr_subst {S S'} (env : interp_scope S')
    (δ : S [⇒] S') e :
    interp_expr (bind δ e) env ≡ interp_expr e (sub_scope δ env)
  with interp_val_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') e :
    interp_val (bind δ e) env ≡ interp_val e (sub_scope δ env)
  with interp_cont_subst {S S'} (env : interp_scope S')
         (δ : S [⇒] S') K :
    interp_cont (bind δ K) env ≡ interp_cont K (sub_scope δ env).
  Proof.
    - destruct e; simpl; try by repeat f_equiv.
      + repeat f_equiv. repeat (intro; simpl; repeat f_equiv).
        rewrite interp_expr_subst. f_equiv.
        intros [|a]; simpl; repeat f_equiv. rewrite interp_expr_ren.
        f_equiv. intro. done.
    - destruct e; simpl.
      + reflexivity.
      + clear -interp_expr_subst.
        apply bi.siProp.internal_eq_soundness.
        iLöb as "IH".
        rewrite {2}interp_rec_unfold.
        rewrite {2}(interp_rec_unfold (interp_expr e)).
        do 1 iApply f_equivI. iNext.
        iApply internal_eq_pointwise.
        rewrite /ir_unf. iIntros (x). simpl.
        rewrite interp_expr_subst.
        iApply f_equivI.
        iApply internal_eq_pointwise.
        iIntros (y').
        destruct y' as [| [| y]]; simpl; first done.
        * by iRewrite - "IH".
        * do 2 rewrite interp_expr_ren.
          iApply f_equivI.
          iApply internal_eq_pointwise.
          iIntros (z).
          done.
      + repeat f_equiv. intro. simpl. repeat f_equiv.
        by rewrite interp_cont_subst.
    - destruct K; simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_subst || apply interp_val_subst || apply interp_cont_subst).
  Qed.



  (** ** Interpretation is a homomorphism (for some constructors) *)

  #[global] Instance interp_cont_hom_emp {S} env :
    IT_hom (interp_cont (END : cont S) env).
  Proof.
    simple refine (IT_HOM _ _ _ _ _); intros; auto.
    simpl. f_equiv. intro. simpl.
    by rewrite laterO_map_id.
  Qed.


  #[global] Instance interp_cont_hom_if {S}
    (K : cont S) (e1 e2 : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (IfK e1 e2 K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite -hom_tick -IF_Tick.
    - trans (Vis op i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (IF t (interp_expr e1 env) (interp_expr e2 env)))
          y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      by rewrite -hom_vis.
    - trans (interp_cont K env (Err e)); first (f_equiv; apply IF_Err).
      apply hom_err.
  Qed.


  #[global] Instance interp_cont_hom_appr {S} (K : cont S)
    (e : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppRK e K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[global] Instance interp_cont_hom_appl {S} (K : cont S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppLK v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv. apply APP'_Tick_l. apply interp_val_asval.
    - trans (Vis op i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (t ⊙ (interp_val v env)))
          y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      by rewrite -hom_vis.
    - trans (interp_cont K env (Err e));
        first (f_equiv; apply APP'_Err_l; apply interp_val_asval).
      apply hom_err.
  Qed.

  #[global] Instance interp_cont_hom_natopr {S} (K : cont S)
    (e : expr S) op env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpRK op e K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite !hom_tick.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[global] Instance interp_cont_hom_natopl {S} (K : cont S)
    (v : val S) op (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (NatOpLK op v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv. by rewrite -NATOP_ITV_Tick_l.
    - trans (Vis op0 i (laterO_map (λne y,
        (λne t : IT, interp_cont K env (NATOP (do_natop op) t (interp_val v env))) y) ◎ ko));
        last (simpl; do 3 f_equiv; by intro).
      rewrite NATOP_ITV_Vis_l hom_vis. f_equiv. intro. simpl.
      by rewrite -laterO_map_compose.
    - trans (interp_cont K env (Err e)).
      + f_equiv. by apply NATOP_Err_l, interp_val_asval.
      + apply hom_err.
  Qed.


  Lemma get_fun_ret' E A `{Cofe A} n : (∀ f, @get_fun E A _ f (core.Ret n) ≡ Err RuntimeErr).
  Proof.
    intros.
    by rewrite IT_rec1_ret.
  Qed.


  #[global] Instance interp_cont_hom {S}
    (K : cont S) env :
    IT_hom (interp_cont K env).
  Proof.
    induction K; simpl; apply _.
  Qed.


  (** ** Finally, preservation of reductions *)
  Lemma interp_cred_no_reify {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) n :
    C ===> C' / (n, 0) ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    t ≡ Tick_n n $ t'.
  Proof.
    inversion 1; cbn-[IF APP' Tick get_ret2]; intros Ht Ht'; inversion Ht; inversion Ht'; try done.
    - rewrite -hom_tick. f_equiv.
      erewrite APP_APP'_ITV; last apply _.
      trans (interp_cont k env (APP (Fun (Next (ir_unf (interp_expr e) env))) (Next $ interp_val v env))).
      { repeat f_equiv. apply interp_rec_unfold. }
      rewrite APP_Fun. simpl. rewrite hom_tick. do 2 f_equiv.
      simplify_eq.
      rewrite !interp_expr_subst.
      f_equiv.
      intros [| [| x]]; simpl; [| reflexivity | reflexivity].
      rewrite interp_val_ren.
      f_equiv.
      intros ?; simpl; reflexivity.
    - rewrite -!hom_tick.
      erewrite APP_APP'_ITV; last apply _.
      rewrite APP_Fun. simpl.
      f_equiv. rewrite -Tick_eq !hom_tick.
      do 2 f_equiv. simpl.
      replace (interp_val v env) with (interp_expr (Val v) env) by done.
      by rewrite -!interp_comp fill_comp.
    - subst.
      destruct n0; simpl.
      + by rewrite IF_False; last lia.
      + by rewrite IF_True; last lia.
    - do 2 f_equiv. simplify_eq.
      destruct v1,v0; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
  Qed.


  Opaque map_meta_cont.
  Opaque extend_scope.
  Opaque Ret.

  Lemma interp_cred_yes_reify {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) (σr : gState_rest sR_idx rs ♯ IT) n :
    C ===> C' / (n, 1) ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    reify (gReifiers_sReifier rs) t (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ t').
  Proof.
    inversion 1; cbn-[IF APP' Tick get_ret2 gState_recomp]; intros Ht Ht'; inversion Ht; inversion Ht'; subst;
      try rewrite !map_meta_cont_cons in Ht, Ht'|-*.
    - trans (reify (gReifiers_sReifier rs)
               (RESET_ (laterO_map (get_val META ◎ (interp_cont k env)))
               (Next (interp_expr e env)))
               (gState_recomp σr (sR_state (map_meta_cont mk env)))
            ).
      {
        repeat f_equiv. rewrite !hom_vis. simpl. f_equiv.
        rewrite ccompose_id_l. by intro.
      }
      rewrite reify_vis_eq//; last first.
      {
        epose proof (@subReifier_reify sz reify_delim rs _ IT _ (op_reset)
                       (laterO_map (get_val META) (Next (interp_expr e env)))
                       _ (laterO_map (get_val META ◎ interp_cont k env)) (map_meta_cont mk env)
                       (laterO_map (get_val META ◎ interp_cont k env) :: map_meta_cont mk env) σr) as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last done.  solve_proper.
      }
      f_equiv. by rewrite laterO_map_Next.
    - 



  Lemma interp_expr_fill_yes_reify {S} K K' Ko env (e e' : expr S)
    (σ σ' : state)
    (σr : gState_rest sR_idx rs ♯ IT) n :
    head_step e K e' K' Ko (n, 1) →
    some_relation K Ko σ ->
    some_relation K' Ko σ ->
    reify (gReifiers_sReifier rs)
      (interp_expr (fill K e) env) (gState_recomp σr (sR_state σ))
      ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K' e') env).
  Proof.
    intros Hst H1. apply (interp_ectx_hom K env) in H1.
    trans (reify (gReifiers_sReifier rs) (interp_ectx K env (interp_expr e env))
             (gState_recomp σr (sR_state σ))).
    { f_equiv. by rewrite interp_comp. }
    inversion Hst; simplify_eq; cbn-[gState_recomp].
    - trans (reify (gReifiers_sReifier rs) (INPUT (interp_ectx K' env ◎ Ret)) (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv; eauto.
        rewrite hom_INPUT.
        do 2 f_equiv. by intro.
      }
      rewrite reify_vis_eq //; first last.
      {
        epose proof (@subReifier_reify sz reify_io rs _ IT _ (inl ()) () (Next (interp_ectx K' env (Ret n0))) (NextO ◎ (interp_ectx K' env ◎ Ret)) σ σ' σr) as H.
        simpl in H.
        simpl.
        erewrite <-H; last first.
        - rewrite H8. reflexivity.
        - f_equiv;
          solve_proper.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
    - trans (reify (gReifiers_sReifier rs) (interp_ectx K' env (OUTPUT n0)) (gState_recomp σr (sR_state σ))).
      {
        do 3 f_equiv; eauto.
        rewrite get_ret_ret//.
      }
      trans (reify (gReifiers_sReifier rs) (OUTPUT_ n0 (interp_ectx K' env (Ret 0))) (gState_recomp σr (sR_state σ))).
      {
        do 2 f_equiv; eauto.
        by rewrite hom_OUTPUT_.
      }
      rewrite reify_vis_eq //; last first.
      {
        epose proof (@subReifier_reify sz reify_io rs _ IT _ op_output
                       n0 (Next (interp_ectx K' env ((Ret 0))))
                       (constO (Next (interp_ectx K' env ((Ret 0)))))
                       σ (update_output n0 σ) σr) as H.
        simpl in H.
        simpl.
        erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. by rewrite /prod_map H0.
        + do 2 f_equiv. by intro.
      }
      repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv.
      rewrite interp_comp.
      reflexivity.
    - match goal with
      | |- context G
             [(ofe_mor_car _ _ (get_fun (?g))
                 ?e)] => set (f := g)
      end.
      match goal with
      | |- context G [(?s, _)] => set (gσ := s) end.
      (* Transparent SHIFT. *)
      (* unfold SHIFT. *)
      set (subEff1 := @subReifier_subEff sz reify_io rs subR).
      trans (reify (gReifiers_sReifier rs)
               (interp_ectx' K env
                  (get_fun f (Fun (Next (ir_unf (interp_expr e0) env))))) gσ).
      { repeat f_equiv. apply interp_rec_unfold. }
      trans (reify (gReifiers_sReifier rs)
               (interp_ectx K env
                  (f (Next (ir_unf (interp_expr e0) env)))) gσ).
      { repeat f_equiv. apply get_fun_fun. }
      subst f.
      Opaque interp_ectx.
      simpl.
      match goal with
      | |- context G [(ofe_mor_car _ _ SHIFT ?g)] => set (f := g)
      end.
      trans (reify (gReifiers_sReifier rs)
               (SHIFT_ f (laterO_map (λne y, interp_ectx K env y) ◎ idfun)) gσ).
      {
        do 2 f_equiv.
        rewrite -(@hom_SHIFT_ F R CR subEff1 idfun f _).
        by f_equiv.
      }
      rewrite reify_vis_eq//; last first.
      {
        simpl.
        epose proof (@subReifier_reify sz reify_io rs subR IT _
                       op_shift f _
                       (laterO_map (interp_ectx K env)) σ' σ' σr) as H.
        simpl in H.
        erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. by rewrite /prod_map H2.
        + do 3f_equiv; try done. by intro.
      }
      clear f.
      f_equiv.
      rewrite -Tick_eq. f_equiv.
      rewrite !interp_expr_subst. f_equiv.
      intros [|[|x]]; eauto. simpl.
      Transparent extend_scope.
      simpl. repeat f_equiv. intro. simpl.
      rewrite laterO_map_Next -Tick_eq. f_equiv.
      rewrite interp_expr_ren interp_comp. simpl.
      symmetry.
      etrans; first by apply interp_ectx_ren.
      repeat f_equiv. unfold ren_scope. simpl. by intro.
      (* rewrite APP'_Fun_r. *)
      (* match goal with *)
      (* | |- context G [(ofe_mor_car _ _ (ofe_mor_car _ _ APP _) ?f)] => *)
      (*     trans (APP (Fun $ Next $ ir_unf (interp_expr e0) env) f); last first *)
      (* end. *)
      (* { repeat f_equiv; try by rewrite interp_rec_unfold. } *)
      (* rewrite APP_Fun -!Tick_eq. simpl. *)
      (* repeat f_equiv. *)
      (* intro. simpl. *)
      (* rewrite interp_comp laterO_map_Next -Tick_eq. f_equiv. *)
      (* symmetry. *)
      (* Transparent extend_scope. *)
      (* fold (@interp_ectx S K env). *)
      (* Opaque interp_ectx. *)
      (* simpl. *)
      (* etrans; first by apply interp_ectx_ren. *)
      (* repeat f_equiv. *)
      (* unfold ren_scope. simpl. *)
      (* apply ofe_mor_ext. done. *)
      (* Transparent interp_ectx. *)
      (* Opaque extend_scope. *)
    - Transparent RESET. unfold RESET.
      trans (reify (gReifiers_sReifier rs)
               (RESET_ (laterO_map (λne y, interp_ectx' K' env y) ◎
                          (laterO_map (λne y, get_val idfun y)) ◎
                          idfun)
                  (Next (interp_val v env)))
            (gState_recomp σr (sR_state σ'))).
      {
        do 2 f_equiv; last done.
        rewrite !hom_vis. simpl. f_equiv.
        by intro x.
      }
      rewrite reify_vis_eq//; last first.
      {
        simpl.
        epose proof (@subReifier_reify sz reify_io rs subR IT _
                       op_reset (Next (interp_val v env)) _
                       (laterO_map (interp_ectx K' env) ◎
                                   laterO_map (get_val idfun)) σ' σ' σr) as H.
        simpl in H. erewrite <-H; last reflexivity.
        f_equiv.
        + intros ???. by rewrite /prod_map H0.
        + do 2 f_equiv. by intro x.
      }
      f_equiv.
      rewrite laterO_map_Next -Tick_eq. f_equiv.
      rewrite interp_comp. f_equiv.
      simpl. by rewrite get_val_ITV.
  Qed.


  (* Lemma soundness_Ectx {S} (e1 e2 e'1 e'2 : expr S) σ1 σ2 (K1 K2 : ectx S) *)
  (*   (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) : *)
  (*   ResetK ∉ K1 -> *)
  (*   e1 = (K1 ⟪ e'1 ⟫)%syn -> *)
  (*   e2 = (K2 ⟪ e'2 ⟫)%syn -> *)
  (*   head_step e'1 σ1 K1 e'2 σ2 K2 (n, m) -> *)
  (*   ssteps (gReifiers_sReifier rs) *)
  (*     (interp_expr e1 env) (gState_recomp σr (sR_state σ1)) *)
  (*     (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n. *)
  (* Proof. *)
  (*   Opaque gState_decomp gState_recomp. *)
  (*   intros. simplify_eq/=. *)
  (*     destruct (head_step_io_01 _ _ _ _ _ _ _ _ H2); subst. *)
  (*     - assert (σ1 = σ2) as ->. *)
  (*       { eapply head_step_no_io; eauto. } *)
  (*       unshelve eapply (interp_expr_fill_no_reify K1) in H2; first apply env; last apply H. *)
  (*       rewrite H2. *)
  (*       rewrite interp_comp. *)
  (*       eapply ssteps_tick_n. *)
  (*     - specialize (interp_ectx_hom K1 env H) as Hhom. *)
  (*       inversion H2;subst. *)
  (*       + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr) in H2; last apply H. *)
  (*         rewrite interp_comp. simpl. *)
  (*         rewrite hom_INPUT. *)
  (*         change 1 with (Nat.add 1 0). econstructor; last first. *)
  (*         { apply ssteps_zero; reflexivity. } *)
  (*         eapply sstep_reify. *)
  (*         { Transparent INPUT. unfold INPUT. simpl. *)
  (*           f_equiv. reflexivity. } *)
  (*         simpl in H2. *)
  (*         rewrite -H2. *)
  (*         repeat f_equiv; eauto. *)
  (*         rewrite interp_comp hom_INPUT. *)
  (*         eauto. *)
  (*       + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H. *)
  (*         rewrite interp_comp. simpl. *)
  (*         rewrite get_ret_ret. *)
  (*         rewrite hom_OUTPUT_. *)
  (*         change 1 with (Nat.add 1 0). econstructor; last first. *)
  (*         { apply ssteps_zero; reflexivity. } *)
  (*         eapply sstep_reify. *)
  (*         { Transparent OUTPUT_. unfold OUTPUT_. simpl. *)
  (*           f_equiv. reflexivity. } *)
  (*         simpl in H. *)
  (*         rewrite -H. *)
  (*         repeat f_equiv; eauto. *)
  (*         Opaque OUTPUT_. *)
  (*         rewrite interp_comp /= get_ret_ret hom_OUTPUT_. *)
  (*         eauto. *)
  (*       + eapply (interp_expr_fill_yes_reify K1 [] env _ _ _ _ σr _ H2) in H. *)
  (*         rewrite !interp_comp. *)
  (*         Opaque interp_ectx. simpl. *)
  (*         match goal with *)
  (*         | |- context G [ofe_mor_car _ _ (get_fun _) ?g] => set (f := g) *)
  (*         end. *)
  (*         assert (f ≡ Fun $ Next $ ir_unf (interp_expr e) env) as -> by apply interp_rec_unfold. *)
  (*         rewrite get_fun_fun. *)
  (*         simpl. *)
  (*         econstructor; last constructor; last done; last done. *)
  (*         eapply sstep_reify. *)
  (*         { rewrite hom_SHIFT_. simpl. *)
  (*           f_equiv. reflexivity. } *)
  (*         simpl in H. rewrite -H. repeat f_equiv. *)
  (*         rewrite interp_comp. f_equiv. simpl. *)
  (*         match goal with *)
  (*           |- context G [ ofe_mor_car _ _ (get_fun ?g)] => set (gi := g) *)
  (*           end. *)
  (*         trans (get_fun gi *)
  (*                  (Fun $ Next $ ir_unf (interp_expr e) env)); last by rewrite interp_rec_unfold. *)
  (*         rewrite get_fun_fun. simpl. reflexivity. *)
  (*       + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H. *)
  (*         rewrite !interp_comp.  *)
  (*         econstructor; last constructor; last done; last done. *)
  (*         eapply sstep_reify. *)
  (*         { simpl. rewrite !hom_vis. reflexivity. } *)
  (*         simpl in H2. *)
  (*         trans (gState_recomp σr (sR_state σ2), *)
  (*                  Tick (interp_expr (K2 ⟪ v ⟫)%syn env)); *)
  (*           last by (repeat f_equiv; apply interp_comp). *)
  (*         rewrite -H. repeat f_equiv. by rewrite interp_comp. *)
  (* Qed. *)

  Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m (env : interp_scope S) :
    prim_step e1 σ1 e2 σ2 (n,m) →
    ssteps (gReifiers_sReifier rs)
              (interp_expr e1 env) (gState_recomp σr (sR_state σ1))
              (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n.
  Proof.
    Opaque gState_decomp gState_recomp.
    inversion 1; simplify_eq/=.
    rewrite !interp_comp.
    pose proof (shift_context_no_reset K Ki Ko H0).
    destruct (head_step_io_01 _ _ _ _ _ _ _ _ _ H1); subst.
      - assert (σ1 = σ2) as ->.
        { eapply head_step_no_io; eauto. }
        unshelve eapply (interp_expr_fill_no_reify Ki) in H1; first apply env; last apply H2.
        rewrite H1.
        rewrite interp_comp.
        eapply ssteps_tick_n.
      - specialize (interp_ectx_hom K1 env H) as Hhom.
        inversion H2;subst.
        + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr) in H2; last apply H.
          rewrite interp_comp. simpl.
          rewrite hom_INPUT.
          change 1 with (Nat.add 1 0). econstructor; last first.
          { apply ssteps_zero; reflexivity. }
          eapply sstep_reify.
          { Transparent INPUT. unfold INPUT. simpl.
            f_equiv. reflexivity. }
          simpl in H2.
          rewrite -H2.
          repeat f_equiv; eauto.
          rewrite interp_comp hom_INPUT.
          eauto.
        + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H.
          rewrite interp_comp. simpl.
          rewrite get_ret_ret.
          rewrite hom_OUTPUT_.
          change 1 with (Nat.add 1 0). econstructor; last first.
          { apply ssteps_zero; reflexivity. }
          eapply sstep_reify.
          { Transparent OUTPUT_. unfold OUTPUT_. simpl.
            f_equiv. reflexivity. }
          simpl in H.
          rewrite -H.
          repeat f_equiv; eauto.
          Opaque OUTPUT_.
          rewrite interp_comp /= get_ret_ret hom_OUTPUT_.
          eauto.
        + eapply (interp_expr_fill_yes_reify K1 [] env _ _ _ _ σr _ H2) in H.
          rewrite !interp_comp.
          Opaque interp_ectx. simpl.
          match goal with
          | |- context G [ofe_mor_car _ _ (get_fun _) ?g] => set (f := g)
          end.
          assert (f ≡ Fun $ Next $ ir_unf (interp_expr e) env) as -> by apply interp_rec_unfold.
          rewrite get_fun_fun.
          simpl.
          econstructor; last constructor; last done; last done.
          eapply sstep_reify.
          { rewrite hom_SHIFT_. simpl.
            f_equiv. reflexivity. }
          simpl in H. rewrite -H. repeat f_equiv.
          rewrite interp_comp. f_equiv. simpl.
          match goal with
            |- context G [ ofe_mor_car _ _ (get_fun ?g)] => set (gi := g)
            end.
          trans (get_fun gi
                   (Fun $ Next $ ir_unf (interp_expr e) env)); last by rewrite interp_rec_unfold.
          rewrite get_fun_fun. simpl. reflexivity.
        + eapply (interp_expr_fill_yes_reify K2 K2 env _ _ _ _ σr _ H2) in H.
          rewrite !interp_comp.
          econstructor; last constructor; last done; last done.
          eapply sstep_reify.
          { simpl. rewrite !hom_vis. reflexivity. }
          simpl in H2.
          trans (gState_recomp σr (sR_state σ2),
                   Tick (interp_expr (K2 ⟪ v ⟫)%syn env));
            last by (repeat f_equiv; apply interp_comp).
          rewrite -H. repeat f_equiv. by rewrite interp_comp.




  (*   unshelve epose proof (soundness_Ectx (Ki ⟪ e0 ⟫)%syn (Ki' ⟪ e3 ⟫)%syn e0 e3 σ1 σ2 Ki Ki' σr n m env H2 _ _ H1 ); try done. *)
  (*   pose proof (shift_context_app K Ki Ko H0) as ->. *)
  (*   pose proof (interp_val_asval v (D := env)). *)
  (*   rewrite get_val_ITV. *)
  (*   simpl. *)
  (*   rewrite get_fun_fun. *)
  (*   simpl. *)
  (*   change 2 with (Nat.add (Nat.add 1 1) 0). *)
  (*   econstructor; last first. *)
  (*   { apply ssteps_tick_n. } *)
  (*   eapply sstep_reify; first (rewrite hom_vis; reflexivity). *)
  (*   match goal with *)
  (*   | |- context G [ofe_mor_car _ _ _ (Next ?f)] => set (f' := f) *)
  (*   end. *)
  (*   trans (reify (gReifiers_sReifier rs) (THROW (interp_val v env) (Next f')) (gState_recomp σr (sR_state σ2))). *)
  (*   { *)
  (*     f_equiv; last done. *)
  (*     f_equiv. *)
  (*     rewrite hom_vis. *)
  (*     Transparent THROW. *)
  (*     unfold THROW. *)
  (*     simpl. *)
  (*     repeat f_equiv. *)
  (*     intros x; simpl. *)
  (*     destruct ((subEff_outs ^-1) x). *)
  (*   } *)
  (*   rewrite reify_vis_eq; first (rewrite Tick_eq; reflexivity). *)
  (*   simpl. *)
  (*   match goal with *)
  (*   | |- context G [(_, _, ?a)] => set (κ := a) *)
  (*   end. *)
  (*   epose proof (@subReifier_reify sz reify_io rs subR IT _ *)
  (*                  (inr (inr (inr (inl ())))) (Next (interp_val v env), Next f') *)
  (*                  (Next (Tau (Next ((interp_ectx K' env) (interp_val v env))))) *)
  (*                  (Empty_setO_rec _) σ2 σ2 σr) as H'. *)
  (*   subst κ. *)
  (*   simpl in H'. *)
  (*   erewrite <-H'; last reflexivity. *)
  (*   rewrite /prod_map. *)
  (*   f_equiv; first solve_proper. *)
  (*   do 2 f_equiv; first reflexivity. *)
  (*   intro; simpl. *)
  (*   f_equiv. *)
  (*   } *)
  (* Qed. *)

End interp.
#[global] Opaque INPUT OUTPUT_ CALLCC THROW.
