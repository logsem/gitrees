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
Program Definition popE : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := Empty_setO;
  |}.

(* apply continuation, pushes outer context in meta *)
Program Definition appContE : opInterp :=
  {|
    Ins := (▶ ∙ * (▶ (∙ -n> ∙)));
    Outs := ▶ ∙;
  |} .

Definition delimE := @[shiftE; resetE; popE;appContE].



Notation op_shift := (inl ()).
Notation op_reset := (inr (inl ())).
Notation op_pop := (inr (inr (inl ()))).
Notation op_app_cont := (inr (inr (inr (inl ())))).



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


  Definition reify_pop : (laterO X) * state * (Empty_setO -n> laterO X) →
                           option (laterO X * state) :=
    λ '(e, σ, _),
      match σ with
      | [] => Some (e, σ)
      | k' :: σ' => Some (k' e, σ')
      end.
  #[export] Instance reify_pop_ne :
    NonExpansive (reify_pop :
        prodO (prodO (laterO X) state) (Empty_setO -n> laterO X) →
        optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. by repeat f_equiv. Qed.


  Definition reify_app_cont : ((laterO X * (laterO (X -n> X))) * state * (laterO X -n> laterO X)) →
                              option (laterO X * state) :=
  λ '((e, k'), σ, k),
    Some (((laterO_ap k' : laterO X -n> laterO X) e : laterO X), k::σ : state).
  #[export] Instance reify_app_cont_ne :
    NonExpansive (reify_app_cont :
        prodO (prodO (prodO (laterO X) (laterO (X -n> X))) state)
          (laterO X -n> laterO X) →
        optionO (prodO (laterO X) (state))).
  Proof.
    intros ?[[[]]][[[]]]?. rewrite /reify_app_cont.
    repeat f_equiv; apply H.
  Qed.

End reifiers.

Canonical Structure reify_delim : sReifier.
Proof.
  simple refine {|
             sReifier_ops := delimE;
             sReifier_state := stateF
           |}.
  intros X HX op.
  destruct op as [ | [ | [ | [| []]]]]; simpl.
  - simple refine (OfeMor (reify_shift)).
  - simple refine (OfeMor (reify_reset)).
  - simple refine (OfeMor (reify_pop)).
  - simple refine (OfeMor (reify_app_cont)).
Defined.



Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff delimE E}.
  Context {subOfe0 : SubOfe natO A}.
  Context {subOfe1 : SubOfe unitO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).



  (** ** POP *)

  Program Definition POP : IT -n> IT :=
    λne e, Vis (E:=E) (subEff_opid op_pop)
             (subEff_ins (F:=delimE) (op:=op_pop) (Next e))
             (Empty_setO_rec _ ◎ (subEff_outs (F:=delimE) (op:=op_pop))^-1).
  Solve All Obligations with solve_proper.

  Notation 𝒫 := (get_val POP).

  (** ** RESET *)

  Program Definition RESET_ : (laterO IT -n> laterO IT) -n>
                                laterO IT -n>
                                IT :=
    λne k e, Vis (E:=E) (subEff_opid op_reset)
               (subEff_ins (F := delimE) (op := op_reset) (laterO_map 𝒫 e))
               (k ◎ subEff_outs (F := delimE) (op := op_reset)^-1).
  Solve Obligations with solve_proper.

  Program Definition RESET : laterO IT -n> IT :=
    RESET_ idfun.

  (** ** SHIFT *)

  Program Definition SHIFT_ : ((laterO IT -n> laterO IT) -n> laterO IT) -n>
                                (laterO IT -n> laterO IT) -n>
                                IT :=
    λne f k, Vis (E:=E) (subEff_opid op_shift)
             (subEff_ins (F:=delimE) (op:=op_shift) ((laterO_map $ 𝒫) ◎ f))
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


  (** ** APP_CONT *)

  Program Definition APP_CONT_ : laterO IT -n> (laterO (IT -n> IT)) -n>
                                    (laterO IT -n> laterO IT) -n>
                                    IT :=
      λne e k k', Vis (E := E) (subEff_opid op_app_cont)
                    (subEff_ins (F:=delimE) (op:=op_app_cont) (e, k))
                    (k' ◎ (subEff_outs (F:=delimE) (op:=op_app_cont))^-1).
  Solve All Obligations with solve_proper.

  Program Definition APP_CONT : laterO IT -n> (laterO (IT -n> IT)) -n>
                                  IT :=
    λne e k, APP_CONT_ e k idfun.
  Solve All Obligations with solve_proper.

End constructors.

Notation 𝒫 := (get_val POP).

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
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} 𝒫 (later_car ( f (laterO_map k))) @ s {{ Φ }}) -∗
    WP@{rs} (k (SHIFT f)) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold SHIFT. simpl.
    rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ (later_map 𝒫 $ f (laterO_map k)) with "Hs").
    {
      simpl.
      repeat f_equiv.
      - rewrite ccompose_id_l. intro. simpl. by rewrite ofe_iso_21.
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
       WP@{rs} 𝒫 (later_car e) @ s {{ Φ }}) -∗
    WP@{rs} k $ (RESET e) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold RESET. simpl. rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ (laterO_map 𝒫 e) with "Hs").
    - simpl. repeat f_equiv. rewrite ccompose_id_l.
      trans ((laterO_map k) :: σ); last reflexivity.
      f_equiv. intro. simpl. by rewrite ofe_iso_21.
    - reflexivity.
    - iApply "Ha".
  Qed.


  Lemma wp_pop_end (v : ITV)
    Φ s :
    has_substate [] -∗
    ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} IT_of_V v @ s {{ Φ }}) -∗
    WP@{rs} 𝒫 (IT_of_V v) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_subreify _ _ _ _ _ _ _ ((Next $ IT_of_V v)) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_pop_cons (σ : state) (v : ITV) (k : IT -n> IT)
    Φ s :
    has_substate ((laterO_map k) :: σ) -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k $ IT_of_V v @ s {{ Φ }}) -∗
    WP@{rs} 𝒫 (IT_of_V v) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_subreify _ _ _ _ _ _ _ ((laterO_map k (Next $ IT_of_V v))) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_app_cont (σ : state) (e : laterO IT) (k' : laterO (IT -n> IT))
    (k : IT -n> IT) {Hk : IT_hom k}
    Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗
       WP@{rs} later_car (laterO_ap k' e) @ s {{ Φ }}) -∗
    WP@{rs} k (APP_CONT e k') @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold APP_CONT. simpl. rewrite hom_vis.
    iApply (wp_subreify _ _ _ _ _ _ _ (laterO_ap k' e) with "Hs").
    - simpl. do 2 f_equiv.
      trans (laterO_map k :: σ); last reflexivity.
      rewrite ccompose_id_l. f_equiv. intro. simpl. by rewrite ofe_iso_21.
    - reflexivity.
    - iApply "Ha".
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

  (** ** APP_CONT *)

  Program Definition interp_app_cont {A} (k e : A -n> IT) : A -n> IT :=
    λne env, get_val (λne x, get_fun
                               (λne (f : laterO (IT -n> IT)),
                                  APP_CONT (Next x) f)
                               (k env))
                     (e env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_app_cont_ne A : NonExpansive2 (@interp_app_cont A).
  Proof.
    intros n??????. rewrite /interp_app_cont. intro. simpl.
    repeat f_equiv; last done. intro. simpl. by repeat f_equiv.
  Qed.
  (* Typeclasses Opaque interp_app_cont. *)

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
    λne env, (λit x, Tau (laterO_map (𝒫 ◎ K env) (Next x))).
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

  Program Definition interp_app_contrk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app_cont q (λne env, t) env.
  Next Obligation. intros A q K t n ????. done. Qed.
  Next Obligation.
    intros A q K env n ???. simpl. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros A q K n ???. intro. simpl. f_equiv.
    - by f_equiv.
    - f_equiv. f_equiv. intro. simpl. by repeat f_equiv.
  Qed.

  Program Definition interp_app_contlk {A} (q : A -n> IT) (K : A -n> IT -n> IT) :
    A -n> IT -n> IT :=
    λne env t, (K env) $ interp_app_cont (λne env, t) q env.
  Next Obligation. intros A q K t n ????. done. Qed.
  Next Obligation.
    intros A q K env n ???. simpl. repeat f_equiv.
    intro. simpl. by repeat f_equiv.
  Qed.
  Next Obligation.
    intros A q K n ???. intro. simpl. f_equiv.
    - by f_equiv.
    - f_equiv; last by f_equiv. f_equiv.  intro. simpl. repeat f_equiv.
  Qed.

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
    | AppCont e1 e2 => interp_app_cont (interp_expr e1) (interp_expr e2)
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
    | AppContLK v K => interp_app_contlk (interp_val v) (interp_cont K)
    | AppContRK e K => interp_app_contrk (interp_expr e) (interp_cont K)
    | NatOpLK op v K => interp_natoplk op (interp_val v) (interp_cont K)
    | NatOpRK op e K => interp_natoprk op (interp_expr e) (interp_cont K)
    end.

  (** ** Interpretation of configurations *)

  Program Definition map_meta_cont {S} (mk : Mcont S) : @interp_scope F R _ S -n> state :=
    λne env, list_fmap _ _ (λ k, laterO_map (𝒫 ◎ (interp_cont k env))) mk.
  Next Obligation. intros S mk n ???. apply list_fmap_ext_ne. intro. by repeat f_equiv. Qed.

  Lemma map_meta_cont_nil {S} env :
    map_meta_cont ([] : Mcont S) env = [].
  Proof. done. Qed.

  Lemma map_meta_cont_cons {S} (k : cont S) (mk : Mcont S) env :
    map_meta_cont (k::mk) env = (laterO_map (𝒫 ◎ interp_cont k env)) :: (map_meta_cont mk env).
  Proof. done. Qed.

  Program Definition interp_config {S} (C : config S) : @interp_scope F R _  S -n> (prodO IT state) :=
      match C with
      | Cexpr e => λne env, (𝒫 (interp_expr e env), []) : prodO IT state
      | Ceval e K mk => λne env, (𝒫 (interp_cont K env (interp_expr e env)),
                                    map_meta_cont mk env)
      | Ccont K v mk => λne env, (𝒫 (interp_cont K env (interp_val v env)),
                                    map_meta_cont mk env)
      | Cmcont mk v => λne env, (𝒫 (interp_val v env),
                                   map_meta_cont mk env)
      | Cret v => λne env, (interp_val v env, [])
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
      + f_equiv; last by rewrite interp_expr_ren.
        f_equiv. intro. simpl. by f_equiv.
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
    - destruct K; try solve [simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_ren || apply interp_val_ren || apply interp_cont_ren)].
      + intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv.
        intro. simpl. by repeat f_equiv.
      + intro. simpl. f_equiv; eauto. do 2 f_equiv.
        intro. simpl. by repeat f_equiv.
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
  Proof. elim : K e env; eauto.
         intros. simpl. rewrite H. f_equiv. simpl.
         do 2 f_equiv. intro. simpl. by repeat f_equiv.
  Qed.

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
      + f_equiv; last eauto. f_equiv. intro. simpl. by repeat f_equiv.
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
    - destruct K; try solve [simpl; repeat f_equiv; intro; simpl; repeat f_equiv;
        (apply interp_expr_subst || apply interp_val_subst || apply interp_cont_subst)].
      + simpl. intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv. intro. simpl. by repeat f_equiv.
      + simpl. intro. simpl. f_equiv; eauto. f_equiv; eauto. f_equiv. intro. simpl. by repeat f_equiv.
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


  #[global] Instance interp_cont_hom_app_contr {S} (K : cont S)
    (e : expr S) env :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppContRK e K) env).
  Proof.
    intros. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - by rewrite -!hom_tick. 
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      by rewrite -laterO_map_compose.
    - by rewrite !hom_err.
  Qed.

  #[global] Instance interp_cont_hom_app_contl {S} (K : cont S)
    (v : val S) (env : interp_scope S) :
    IT_hom (interp_cont K env) ->
    IT_hom (interp_cont (AppContLK v K) env).
  Proof.
    intros H. simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick. f_equiv.
      rewrite get_val_ITV. simpl. rewrite hom_tick.
      f_equiv. by rewrite get_val_ITV.
    - rewrite get_val_ITV. simpl. rewrite get_fun_vis. rewrite hom_vis.
      f_equiv. intro. simpl. rewrite -laterO_map_compose.
      f_equiv. f_equiv. intro. simpl.
      f_equiv. by rewrite get_val_ITV.
    - rewrite get_val_ITV. simpl. rewrite get_fun_err. apply hom_err.
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
    - do 4 f_equiv. intro. simpl. by repeat f_equiv.
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
    - subst.
      destruct n0; simpl.
      + by rewrite IF_False; last lia.
      + by rewrite IF_True; last lia.
    - do 2 f_equiv. simplify_eq.
      destruct v1,v0; try naive_solver. simpl in *.
      rewrite NATOP_Ret.
      destruct op; simplify_eq/=; done.
  Qed.

  Lemma interp_cred_no_reify_state {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) n :
    C ===> C' / (n, 0) ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    σ = σ'.
  Proof. 
    inversion 1; cbn; intros Ht Ht'; inversion Ht; inversion Ht'; subst; reflexivity.
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
               (RESET_ (laterO_map (𝒫 ◎ (interp_cont k env)))
               (Next (interp_expr e env)))
               (gState_recomp σr (sR_state (map_meta_cont mk env)))).
      {
        repeat f_equiv. rewrite !hom_vis. simpl. f_equiv.
        rewrite ccompose_id_l. by intro.
      }
      rewrite reify_vis_eq//; last first.
      {
        epose proof (@subReifier_reify sz reify_delim rs _ IT _ (op_reset)
                       (laterO_map 𝒫 (Next (interp_expr e env)))
                       _ (laterO_map (𝒫 ◎ interp_cont k env)) (map_meta_cont mk env)
                       (laterO_map (𝒫 ◎ interp_cont k env) :: map_meta_cont mk env) σr) as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last done.  solve_proper.
      }
      f_equiv. by rewrite laterO_map_Next.
    - remember (map_meta_cont mk env) as σ.
      match goal with
      | |- context G [Vis ?o ?f ?κ] => set (fin := f); set (op := o); set (kout := κ)
      end.
      trans (reify (gReifiers_sReifier rs)
               (Vis op fin ((laterO_map (𝒫 ◎ interp_cont k env)) ◎ kout))
               (gState_recomp σr (sR_state σ))).
      {
        repeat f_equiv. rewrite !hom_vis. f_equiv. by intro.
      }
      rewrite reify_vis_eq//; last first.
      {
        epose proof (@subReifier_reify sz reify_delim rs _ IT _ (op_shift)
                       _ _ (laterO_map (𝒫 ◎ interp_cont k env))
                     σ σ σr) as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last first.
        - subst kout. by rewrite ccompose_id_l.
        - subst fin. reflexivity.
        - solve_proper.
      }
      rewrite -Tick_eq. do 3 f_equiv.
      rewrite interp_expr_subst.
      simpl. f_equiv.
      intros [|s]; simpl; eauto.
      Transparent extend_scope.
      simpl. f_equiv. f_equiv. by intro.
      Opaque extend_scope.
    - remember (map_meta_cont mk env) as σ.
      remember (laterO_map (𝒫 ◎ interp_cont k env)) as kk.
      match goal with
      | |- context G [ofe_mor_car _ _ (get_fun _)
                        (ofe_mor_car _ _ Fun ?f)] => set (fin := f)
      end.
      trans (reify (gReifiers_sReifier rs)
               (APP_CONT_ (Next (interp_val v env))
                  fin kk)
            (gState_recomp σr (sR_state (σ)))).
      {
        repeat f_equiv. rewrite get_val_ITV. simpl. rewrite get_fun_fun. simpl.
        rewrite !hom_vis. f_equiv. subst kk. rewrite ccompose_id_l. intro. simpl.
        rewrite laterO_map_compose. done.
      }
      rewrite reify_vis_eq//; last first.
      {
        epose proof (@subReifier_reify sz reify_delim rs _ IT _ (op_app_cont)
                       (Next (interp_val v env), fin) _ kk σ (kk :: σ) σr)
                    as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; eauto. solve_proper.
      }
      f_equiv. by rewrite -!Tick_eq.
    - remember (map_meta_cont mk env) as σ.
      trans (reify (gReifiers_sReifier rs) (POP (interp_val v env))
               (gState_recomp σr (sR_state (laterO_map (𝒫 ◎ interp_cont k env) :: σ)))).
      {
        do 2 f_equiv; last repeat f_equiv.
        apply get_val_ITV.
      }
      rewrite reify_vis_eq//; last first.
      {
        epose proof (@subReifier_reify sz reify_delim rs _ IT _ (op_pop)
                       (Next (interp_val v env)) _ _
                       (laterO_map (𝒫 ◎ interp_cont k env) :: σ) σ σr)
                       as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last reflexivity.
        solve_proper.
      }
      f_equiv. rewrite laterO_map_Next -Tick_eq.
      by f_equiv.
    - trans (reify (gReifiers_sReifier rs) (POP (interp_val v env))
               (gState_recomp σr (sR_state []))).
      {
        do 2 f_equiv; last first.
        { f_equiv. by rewrite map_meta_cont_nil. }
        apply get_val_ITV.
      }
      rewrite reify_vis_eq//; last first.
      {
        epose proof (@subReifier_reify sz reify_delim rs _ IT _ (op_pop)
                       (Next (interp_val v env)) _ _
                       [] [] σr)
                       as Hr.
        simpl in Hr|-*.
        erewrite <-Hr; last reflexivity.
        repeat f_equiv; last reflexivity.
        solve_proper.
      }
      f_equiv. by rewrite -Tick_eq.
  Qed.


  (** * SOUNDNESS *)
  Lemma soundness {S : Set} (env : interp_scope S) (C C' : config S)
    (t t' : IT) (σ σ' : state) (σr : gState_rest sR_idx rs ♯ IT) n nm :
    steps C C' nm ->
    fst nm = n ->
    (interp_config C env) = (t, σ) ->
    (interp_config C' env) = (t', σ') ->
    ssteps (gReifiers_sReifier rs)
      t (gState_recomp σr (sR_state σ))
      t' (gState_recomp σr (sR_state σ')) n.
  Proof.
    intros H.
    revert n t t' σ σ'.
    induction (H); intros n0 t t' σ σ' Hnm Ht Ht'; subst; simpl.
    - rewrite Ht' in Ht. constructor; inversion Ht; done.
    - destruct (interp_config c2 env) as [t2 σ2] eqn:Heqc2.
      assert ((n', m').1 = n') as Hn' by done.
      rewrite <-Heqc2 in IHs.
      specialize (IHs s n' t2 t' σ2 σ' Hn' Heqc2 Ht').
      inversion H0; subst;
        try solve [specialize (interp_cred_no_reify env _ _ _ _ _ _ _ H0 Ht Heqc2) as Heq;
                   specialize (interp_cred_no_reify_state env _ _ _ _ _ _ _ H0 Ht Heqc2) as <-;
                   simpl in Heq|-*; rewrite Heq; eapply IHs];
        try solve
          [eapply ssteps_many with t2 (gState_recomp σr (sR_state σ2)); last done;
            specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H0 Ht Heqc2) as Heq;
            cbn in Ht; eapply sstep_reify; last done;
            inversion Ht; rewrite !hom_vis; done].
      + eapply ssteps_many with t2 (gState_recomp σr (sR_state σ2)); last done.
        specialize (interp_cred_no_reify env _ _ _ _ _ _ _ H0 Ht Heqc2) as Heq.
        specialize (interp_cred_no_reify_state env _ _ _ _ _ _ _ H0 Ht Heqc2) as <-.
        simpl in Heq|-*; rewrite Heq. constructor; eauto.
      + specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H0 Ht Heqc2) as Heq.
        simpl in Heq|-*.
        change (2+n') with (1+(1+n')).
        eapply ssteps_many; last first.
        * eapply ssteps_many with t2 (gState_recomp σr (sR_state σ2)); last done.
          eapply sstep_tick; reflexivity.
        * eapply sstep_reify; last apply Heq.
          cbn in Ht. inversion Ht.
          rewrite get_val_ITV. simpl. rewrite get_fun_fun. simpl.
          rewrite !hom_vis. done.
      + eapply ssteps_many with t2 (gState_recomp σr (sR_state σ2)); last done.
        specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H0 Ht Heqc2) as Heq.
        cbn in Ht; inversion Ht. subst. rewrite get_val_ITV. simpl.
        eapply sstep_reify; simpl in Heq; last first.
        * rewrite -Heq. f_equiv. f_equiv. rewrite get_val_ITV. simpl. done.
        * f_equiv. reflexivity.
      + eapply ssteps_many with t2 (gState_recomp σr (sR_state σ2)); last done.
        specialize (interp_cred_yes_reify env _ _ _ _ _ _ σr _ H0 Ht Heqc2) as Heq.
        cbn in Ht; inversion Ht. subst. rewrite get_val_ITV. simpl.
        eapply sstep_reify; simpl in Heq; last first.
        * rewrite -Heq. repeat f_equiv. by rewrite get_val_ITV.
        * f_equiv. reflexivity.
  Qed.

End interp.
#[global] Opaque SHIFT_ RESET_ POP APP_CONT_.
