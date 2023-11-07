From Equations Require Import Equations.
From gitrees Require Import gitree.
From gitrees.input_lang Require Import lang.
Require Import gitrees.lang_generic_sem.

Require Import Binding.Lib.

Notation stateO := (leibnizO state).

Program Definition inputE : opInterp := {|
                                         Ins := unitO;
                                         Outs := natO;
                                       |}.
Program Definition outputE : opInterp := {|
                                          Ins := natO;
                                          Outs := unitO;
                                        |}.

Definition callccIF : oFunctor := (▶ ∙)%OF.

#[local] Instance callccIF_inhabited X `{!Cofe X, !Inhabited X} : Inhabited (callccIF ♯ X).
Proof.
  constructor.
  unshelve refine (Next inhabitant).
Qed.
#[local] Instance callccIF_cofe X `{!Cofe X} : Cofe (callccIF ♯ X).
Proof. apply _. Qed.
#[local] Instance callccIF_contr : oFunctorContractive callccIF.
Proof.
  intros ???????? n [a b] [c d] H.
  apply laterO_map_contractive.
  destruct n as [| n].
  - apply dist_later_0.
  - apply dist_later_S.
    apply dist_later_S in H.
    destruct H as [H1 H2]; simpl in H1, H2.
    by f_equiv.
Qed.

Definition callccOF : oFunctor := unitO.

#[local] Instance callccOF_inhabited X `{!Cofe X, !Inhabited X} : Inhabited (callccOF ♯ X).
Proof.
  constructor.
  simpl.
  constructor.
Qed.
#[local] Instance callccOF_cofe X `{!Cofe X} : Cofe (callccOF ♯ X).
Proof. apply _. Qed.
#[local] Instance callccOF_contr : oFunctorContractive callccOF.
Proof.
  intros ???????? n [a b] [c d] H.
  solve_proper.
Qed.

Program Definition callccE : opInterp :=  {|
                                          Ins := callccIF;
                                          Outs := callccOF;
                                        |}.

Definition throwIF : oFunctor := (▶ ∙ * ▶ ∙)%OF.

#[local] Instance throwIF_inhabited X `{!Cofe X, !Inhabited X} : Inhabited (throwIF ♯ X).
Proof.
  constructor.
  unshelve refine (Next inhabitant, Next inhabitant).
Qed.
#[local] Instance throwIF_cofe X `{!Cofe X} : Cofe (throwIF ♯ X).
Proof. apply _. Qed.
#[local] Instance throwIF_contr : oFunctorContractive throwIF.
Proof.
  intros ???????? n [a b] [c d] H.
  simpl.
  f_equiv.
  {
    apply laterO_map_contractive.
    destruct n as [| n].
    - apply dist_later_0.
    - apply dist_later_S.
      apply dist_later_S in H.
      destruct H as [H1 H2]; simpl in H1, H2.
      assumption.
  }
  {
    apply laterO_map_contractive.
    destruct n as [| n].
    - apply dist_later_0.
    - apply dist_later_S.
      apply dist_later_S in H.
      destruct H as [H1 H2]; simpl in H1, H2.
      assumption.
  }
Qed.

Definition throwOF : oFunctor := unitO.

#[local] Instance throwOF_inhabited X `{!Cofe X, !Inhabited X} : Inhabited (throwOF ♯ X).
Proof.
  constructor.
  apply (Next inhabitant).
Qed.
#[local] Instance throwOF_cofe X `{!Cofe X} : Cofe (throwOF ♯ X).
Proof. apply _. Qed.
#[local] Instance throwOF_contr : oFunctorContractive throwOF.
Proof.
  intros ???????? n [a b] [c d] H.
  unfold throwOF; simpl.
  reflexivity.
Qed.

Program Definition throwE : opInterp :=  {|
  Ins := throwIF;
  Outs := throwOF;
|}.

Definition ioE := @[inputE;outputE;callccE;throwE].

(* Canonical Structure reify_io : sReifier. *)
(* Proof. *)
(*   simple refine {| sReifier_ops := ioE; *)
(*                    sReifier_state := stateO *)
(*                 |}. *)
(*   intros X HX op. *)
(*   destruct op as [ | [ | [ | [| []]]]]; simpl. *)
(*   - simple refine (λne (us : prodO (prodO unitO stateO) (natO -n> laterO X)), *)
(*        Some $ update_input (sndO (fstO us)) : optionO (prodO natO stateO)). *)
(*     intros n [[] s1] [[] s2] [[Hs1 Hs2] Hs]; simpl in *. *)
(*     repeat f_equiv. apply Hs2. *)
(*   - simple refine (λne (us : prodO (prodO natO stateO) (unitO -n> laterO X)), *)
(*        Some $ ((), update_output (fstO (fstO us)) (sndO (fstO us))) : optionO (prodO unitO stateO)). *)
(*     intros n [m s1] [m' s2] [-> Hs]. solve_proper. *)
(*   - simple refine (λne (us : prodO (prodO (laterO X) stateO) (unitO -n> laterO X)), Some $ ((), sndO (fstO us))). *)
(*     solve_proper. *)
(*   - simple refine (λne (us : prodO (prodO (prodO (laterO X) (laterO X)) stateO) (unitO -n> laterO X)), _). *)
(*     + destruct us as [[[us0 us1] us2] us3]. *)
(*       (* if us1 is next(fun(k)) some k(us0) else none *) *)
(*       admit. *)
(*     + admit. *)
(* Admitted. *)

(* reify throw (x, next(fun(κ))) σ _ = (κ x) *)
(* reify throw _ _ _ = Error      *)

Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff ioE E}.
  Context {subOfe0 : SubOfe natO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  Program Definition INPUT : (nat -n> IT) -n> IT := λne k, Vis (E:=E) (subEff_opid (inl ()))
                                                             (subEff_ins (F:=ioE) (op:=(inl ())) ())
                                                             (NextO ◎ k ◎ (subEff_outs (F:=ioE) (op:=(inl ())))^-1).
  Solve Obligations with solve_proper.
  Program Definition OUTPUT_ : nat -n> IT -n> IT :=
    λne m α, Vis (E:=E) (subEff_opid (inr (inl ())))
                        (subEff_ins (F:=ioE) (op:=(inr (inl ()))) m)
                        (λne _, NextO α).
  Solve All Obligations with solve_proper_please.
  Program Definition OUTPUT : nat -n> IT := λne m, OUTPUT_ m (Ret 0).

  Lemma hom_INPUT k f `{!IT_hom f} : f (INPUT k) ≡ INPUT (OfeMor f ◎ k).
  Proof.
    unfold INPUT.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map]. rewrite laterO_map_Next.
    done.
  Qed.
  Lemma hom_OUTPUT_ m α f `{!IT_hom f} : f (OUTPUT_ m α) ≡ OUTPUT_ m (f α).
  Proof.
    unfold OUTPUT.
    rewrite hom_vis/=. repeat f_equiv.
    intro x. cbn-[laterO_map]. rewrite laterO_map_Next.
    done.
  Qed.

  (* Program Definition CALLCC : (IT -n> IT) -n> IT -n> IT := *)
  (*   λne k, Vis (E:=E) (subEff_opid (inr (inr (inl ())))) *)
  (*            (subEff_ins (F:=ioE) (op:=(inr (inr (inl ())))) (Next k)) *)
  (*            (NextO ◎ k ◎ (subEff_outs (F:=ioE) (op:=(inr (inr (inl ())))))^-1). *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   simpl. *)
  (* Admit Obligations. *)

  (* Program Definition THROW : IT -n> IT -n> IT := *)
  (*   λne m α, Vis (E:=E) (subEff_opid (inr (inr (inr (inl ()))))) *)
  (*                       (subEff_ins (F:=ioE) (op:=(inr (inr (inr (inl ()))))) _) *)
  (*                       (λne _, NextO α). *)
  (* Admit Obligations. *)

  (* Lemma hom_CALLCC e k f `{!IT_hom f} : f (CALLCC k e) ≡ CALLCC (OfeMor f ◎ k) (f e). *)
  (* Proof. *)
  (*   unfold CALLCC. *)
  (* Admitted. *)
  (* Lemma hom_THROW m n f `{!IT_hom f} : f (THROW m n) ≡ THROW (f m) (f n). *)
  (* Proof. *)
  (* Admitted. *)

End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  (* Context {subR : subReifier reify_io rs}. *)
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  (* Lemma wp_input (σ σ' : stateO) (n : nat) (k : natO -n> IT) Φ s : *)
  (*   update_input σ = (n, σ') → *)
  (*   has_substate σ -∗ *)
  (*   ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} (k n) @ s {{ Φ }}) -∗ *)
  (*   WP@{rs} (INPUT k) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   intros Hs. iIntros "Hs Ha". *)
  (*   unfold INPUT. simpl. *)
  (*   iApply (wp_subreify with "Hs"). *)
  (*   { simpl. by rewrite Hs. } *)
  (*   { simpl. by rewrite ofe_iso_21. } *)
  (*   iModIntro. done. *)
  (* Qed. *)
  (* Lemma wp_output (σ σ' : stateO) (n : nat) Φ s : *)
  (*   update_output n σ = σ' → *)
  (*   has_substate σ -∗ *)
  (*   ▷ (£ 1 -∗ has_substate σ' -∗ Φ (RetV 0)) -∗ *)
  (*   WP@{rs} (OUTPUT n) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   intros Hs. iIntros "Hs Ha". *)
  (*   unfold OUTPUT. simpl. *)
  (*   iApply (wp_subreify with "Hs"). *)
  (*   { simpl. by rewrite Hs. } *)
  (*   { simpl. done. } *)
  (*   iModIntro. iIntros "H1 H2". *)
  (*   iApply wp_val. by iApply ("Ha" with "H1 H2"). *)
  (* Qed. *)

  (* Lemma wp_callcc (σ : stateO) (n : nat) Φ s : *)
  (*   has_substate σ -∗ *)
  (*   ▷ (£ 1 -∗ Φ (RetV 0)) -∗ *)
  (*   WP@{rs} (CALLCC n) @ s {{ Φ }}. *)
  (* Proof. *)
  (*   intros Hs. iIntros "Hs Ha". *)
  (*   unfold OUTPUT. simpl. *)
  (*   iApply (wp_subreify with "Hs"). *)
  (*   { simpl. by rewrite Hs. } *)
  (*   { simpl. done. } *)
  (*   iModIntro. iIntros "H1 H2". *)
  (*   iApply wp_val. by iApply ("Ha" with "H1 H2"). *)
  (* Qed. *)

End weakestpre.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers sz).
  (* Context {subR : subReifier reify_io rs}. *)
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Context {subEff0 : subEff ioE F}.
  (** Interpreting individual operators *)
  Program Definition interp_input {A} : A -n> IT :=
    λne env, INPUT Ret.
  Program Definition interp_output {A} (t : A -n> IT) : A -n> IT :=
    get_ret OUTPUT ◎ t.
  Local Instance interp_ouput_ne {A} : NonExpansive2 (@interp_output A).
  Proof. solve_proper. Qed.

  (* Program Definition interp_callcc {A} (t : A -n> ((IT -n> IT))) (n : A -n> IT) *)
  (*   : A -n> IT := λne env, CALLCC (t env) (n env). *)
  (* Next Obligation. *)
  (*   intros ???. *)
  (*   intros n' x y H. *)
  (*   do 2 f_equiv; solve_proper. *)
  (* Qed. *)

  (* Program Definition interp_throw {A} (n : A -n> IT) (m : A -n> IT) *)
  (*   : A -n> IT := λne env, THROW (n env) (m env). *)
  (* Next Obligation. *)
  (*   intros ???. *)
  (*   intros n' x y H. *)
  (*   do 2 f_equiv; solve_proper. *)
  (* Qed. *)

  Program Definition interp_natop {A} (op : nat_op) (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, NATOP (do_natop op) (t1 env) (t2 env).
  Solve All Obligations with solve_proper_please.

  Global Instance interp_natop_ne A op : NonExpansive2 (@interp_natop A op).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_natop.

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

  Program Definition interp_rec {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT) : @interp_scope F R _ S -n> IT := mmuu (interp_rec_pre body).

  Program Definition ir_unf {S : Set} (body : @interp_scope F R _ (inc (inc S)) -n> IT) env : IT -n> IT :=
    λne a, body (@extend_scope F R _ _ (@extend_scope F R _ _ env (interp_rec body env)) a).
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

  Program Definition interp_app {A} (t1 t2 : A -n> IT) : A -n> IT :=
    λne env, APP' (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_app_ne A : NonExpansive2 (@interp_app A).
  Proof. solve_proper. Qed.
  Typeclasses Opaque interp_app.

  Program Definition interp_if {A} (t0 t1 t2 : A -n> IT) : A -n> IT :=
    λne env, IF (t0 env) (t1 env) (t2 env).
  Solve All Obligations with first [ solve_proper | solve_proper_please ].
  Global Instance interp_if_ne A n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (@interp_if A).
  Proof. solve_proper. Qed.

  Program Definition interp_nat (n : nat) {A} : A -n> IT :=
    λne env, Ret n.

  Program Definition interp_cont {A} (K : A -n> (IT -n> IT)) : A -n> IT := λne env, Fun (Next (K env)).
  Next Obligation.
    solve_proper.
  Qed.

  Program Definition interp_applk {A} (q : A -n> IT) (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) := λne env t, interp_app q (λne env, K env t) env.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.

  Program Definition interp_apprk {A} (K : A -n> (IT -n> IT)) (q : A -n> IT) : A -n> (IT -n> IT) := λne env t, interp_app (λne env, K env t) q env.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.

  Axiom falso : False.

  (** Interpretation for all the syntactic categories: values, expressions, contexts *)
  Fixpoint interp_val {S} (v : val S) : interp_scope S -n> IT :=
    match v with
    | LitV n => interp_nat n
    | VarV x => interp_var x
    | RecV e => interp_rec (interp_expr e)
    | ContV K => interp_cont (interp_ectx K)
    end
  with interp_expr {S} (e : expr S) : interp_scope S -n> IT :=
         match e with
         | Val v => interp_val v
         | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
         | NatOp op e1 e2 => interp_natop op (interp_expr e1) (interp_expr e2)
         | If e e1 e2 => interp_if (interp_expr e) (interp_expr e1) (interp_expr e2)
         | Input => interp_input
         | Output e => interp_output (interp_expr e)
         | Callcc e =>
             (* interp_callcc _ (interp_expr e) *)
             False_rect _ falso
         | Throw e1 e2 =>
             (* interp_throw e1 e2 *)
             False_rect _ falso
         end
  with interp_ectx {S} (K : ectx S) : interp_scope S -n> (IT -n> IT) :=
         match K with
         | EmptyK =>
             λne env, λne t, t
         | AppLK e1 K => interp_applk (interp_expr e1) (interp_ectx K)
         | AppRK K v2 => interp_apprk (interp_ectx K) (interp_val v2)
         | NatOpLK op e1 K =>
             False_rect _ falso
         | NatOpRK op K v2 =>
             False_rect _ falso
         | IfK K e1 e2 =>
             False_rect _ falso
         | OutputK K =>
             False_rect _ falso
         | ThrowLK K e =>
             False_rect _ falso
         | ThrowRK v K =>
             False_rect _ falso
         end.
  Solve All Obligations with first [ solve_proper | solve_proper_please ].

  (* #[global] Instance interp_val_asval {S} (v : val S) D : AsVal (interp_val v D). *)
  (* Proof. *)
  (*   destruct v; simpl; first apply _. *)
  (*   rewrite interp_rec_unfold. apply _. *)
  (* Qed. *)

  (* Lemma interp_ctx_item_fill {S} (Ki : ectx_item S) e env : *)
  (*   interp_expr (fill_item Ki e) env ≡ interp_ctx_item Ki env (interp_expr e env). *)
  (* Proof. destruct Ki; reflexivity. Qed. *)

  (* Lemma interp_ectx_fill {S} (K : ectx S) e env : *)
  (*   interp_expr (fill K e) env ≡ interp_ectx K env (interp_expr e env). *)
  (* Proof. *)
  (*   revert e; induction K as [|Ki K]=>e; first done. *)
  (*   rewrite IHK. simpl. rewrite interp_ctx_item_fill. done. *)
  (* Qed. *)

  (* (** Applying renamings and subsitutions to the interpretation of scopes *) *)
  (* Equations interp_rens_scope {S S' : scope} *)
  (*           (E : interp_scope (E:=F) (R:=R) S') (s : rens S S') : interp_scope (E:=F) (R:=R) S := *)
  (*   interp_rens_scope (S:=[]) E s := tt : interp_scope []; *)
  (*   interp_rens_scope (S:=_::_) E s := *)
  (*     (interp_var (hd_ren s) E, interp_rens_scope E (tl_ren s)). *)

  (* Equations interp_subs_scope {S S' : scope} *)
  (*           (E : interp_scope (E:=F) (R:=R) S') (s : subs S S') : interp_scope (E:=F) (R:=R) S := *)
  (*   interp_subs_scope (S:=[]) E s := tt : interp_scope []; *)
  (*   interp_subs_scope (S:=_::_) E s := *)
  (*     (interp_expr (hd_sub s) E, interp_subs_scope E (tl_sub s)). *)


  (* Global Instance interp_rens_scope_ne S S2 n : *)
  (*   Proper ((dist n) ==> (≡) ==> (dist n)) (@interp_rens_scope S S2). *)
  (* Proof. *)
  (*   intros D D' HE s1 s2 Hs. *)
  (*   induction S as [|τ' S]; simp interp_rens_scope; auto. *)
  (*   f_equiv. *)
  (*   - unfold hd_ren; rewrite Hs. by f_equiv. *)
  (*   - apply IHS. intros v. unfold tl_ren; by rewrite Hs. *)
  (* Qed. *)
  (* Global Instance interp_subs_scope_ne S S2 n : *)
  (*   Proper ((dist n) ==> (≡) ==> (dist n)) (@interp_subs_scope S S2). *)
  (* Proof. *)
  (*   intros D D' HE s1 s2 Hs. *)
  (*   induction S as [|τ' S]; simp interp_subs_scope; auto. *)
  (*   f_equiv. *)
  (*   - unfold hd_sub; by rewrite Hs HE. *)
  (*   - apply IHS. intros v. unfold tl_sub; by rewrite Hs. *)
  (* Qed. *)
  (* Global Instance interp_rens_scope_proper S S2 : *)
  (*   Proper ((≡) ==> (≡) ==> (≡)) (@interp_rens_scope S S2). *)
  (* Proof. *)
  (*   intros D D' HE s1 s2 Hs. *)
  (*   induction S as [|τ' S]; simp interp_rens_scope; auto. *)
  (*   f_equiv. *)
  (*   - unfold hd_ren; rewrite Hs. *)
  (*     by rewrite HE. *)
  (*   - apply IHS. intros v. unfold tl_ren; by rewrite Hs. *)
  (* Qed. *)
  (* Global Instance interp_subs_scope_proper S S2 : *)
  (*   Proper ((≡) ==> (≡) ==> (≡)) (@interp_subs_scope S S2). *)
  (* Proof. *)
  (*   intros D D' HE s1 s2 Hs. *)
  (*   induction S as [|τ' S]; simp interp_subs_scope; auto. *)
  (*   f_equiv. *)
  (*   - unfold hd_sub; by rewrite Hs HE. *)
  (*   - apply IHS. intros v. unfold tl_sub; by rewrite Hs. *)
  (* Qed. *)

  (* (** ** The substituion lemma, for renamings and substitutions *) *)
  (* Lemma interp_rens_scope_tl_ren {S S2} x D (r : rens S S2) : *)
  (*   interp_rens_scope ((x, D) : interp_scope (()::S2)) (tl_ren (rens_lift r)) *)
  (*                   ≡ interp_rens_scope D r. *)
  (* Proof. *)
  (*   induction S as [|τ' S]; simp interp_rens_scope; eauto. *)
  (*   f_equiv. *)
  (*   { unfold hd_ren, tl_ren. simp rens_lift interp_var. *)
  (*     done. } *)
  (*   { rewrite -IHS. f_equiv. clear. *)
  (*     intros v. dependent elimination v; *)
  (*       unfold hd_ren, tl_ren; simp rens_lift; auto. } *)
  (* Qed. *)

  (* Lemma interp_rens_scope_idren {S} (D : interp_scope S) : *)
  (*   interp_rens_scope D (@idren S) ≡ D. *)
  (* Proof. *)
  (*   induction S as [|[] S]; simp interp_rens_scope. *)
  (*   { by destruct D. } *)
  (*   destruct D as [x D]. simp interp_var. simpl. *)
  (*   f_equiv. *)
  (*   trans (interp_rens_scope ((x, D) : interp_scope (()::S)) (tl_ren (rens_lift idren))). *)
  (*   { f_equiv. intros v. unfold tl_ren. *)
  (*     reflexivity. } *)
  (*   rewrite interp_rens_scope_tl_ren. *)
  (*   apply IHS. *)
  (* Qed. *)

  (* Lemma interp_expr_ren {S D : scope} (M : expr S) (r : rens S D) : *)
  (*   ∀ (E : interp_scope D), *)
  (*     interp_expr (ren_expr M r) E ≡ interp_expr M (interp_rens_scope E r) *)
  (* with interp_val_ren {S D : scope} (v : val S) (r : rens S D) : *)
  (*   ∀ (E : interp_scope D), *)
  (*     interp_val (ren_val v r) E ≡ interp_val v (interp_rens_scope E r). *)
  (* Proof. *)
  (*   - revert D r. induction M=> D r D2; simpl; simp ren_expr. *)
  (*     all: try by (simpl; repeat intro; simpl; repeat f_equiv; eauto). *)
  (*     + (* variable *) revert r. *)
  (*       induction v=>r. *)
  (*       * simp interp_var interp_rens_scope. done. *)
  (*       * simp interp_var interp_rens_scope. simpl. *)
  (*         apply (IHv (tl_ren r)). *)
  (*     + (* recursive functions *) simp ren_expr. simpl. *)
  (*       apply bi.siProp.internal_eq_soundness. *)
  (*       iLöb as "IH". *)
  (*       rewrite {2}interp_rec_unfold. *)
  (*       rewrite {2}(interp_rec_unfold (interp_expr M)). *)
  (*       iApply f_equivI. iNext. iApply internal_eq_pointwise. *)
  (*       rewrite /ir_unf. iIntros (x). simpl. *)
  (*       rewrite interp_expr_ren. *)
  (*       iApply f_equivI. *)
  (*       simp interp_rens_scope interp_var. simpl. *)
  (*       rewrite !interp_rens_scope_tl_ren. *)
  (*       iRewrite "IH". *)
  (*       done. *)
  (*   - revert D r. induction v=> D r D2; simpl; simp ren_val; eauto. *)
  (*     (* recursive functions *) *)
  (*     simp ren_expr. simpl. *)
  (*     apply bi.siProp.internal_eq_soundness. *)
  (*     iLöb as "IH". *)
  (*     rewrite {2}interp_rec_unfold. *)
  (*     rewrite {2}(interp_rec_unfold (interp_expr e)). *)
  (*     iApply f_equivI. iNext. iApply internal_eq_pointwise. *)
  (*     rewrite /ir_unf. iIntros (x). simpl. *)
  (*     rewrite interp_expr_ren. *)
  (*     iApply f_equivI. *)
  (*     simp interp_rens_scope interp_var. simpl. *)
  (*     rewrite !interp_rens_scope_tl_ren. *)
  (*     iRewrite "IH". *)
  (*     done. *)
  (* Qed. *)

  (* Lemma interp_subs_scope_tl_sub {S S2} x D (s : subs S S2) : *)
  (*   interp_subs_scope ((x, D) : interp_scope (()::S2)) (tl_sub (subs_lift s)) *)
  (*                   ≡ interp_subs_scope D s. *)
  (* Proof. *)
  (*   induction S as [|[] S]; simp interp_subs_scope; first done. *)
  (*   f_equiv. *)
  (*   { unfold hd_sub, tl_sub. simp subs_lift interp_var. *)
  (*     unfold expr_lift. rewrite interp_expr_ren. f_equiv. *)
  (*     trans (interp_rens_scope ((x, D) : interp_scope (()::S2)) (tl_ren (rens_lift idren))). *)
  (*     { f_equiv. intros v. unfold tl_ren. *)
  (*       simp rens_lift idren. done. } *)
  (*     rewrite interp_rens_scope_tl_ren. *)
  (*     apply interp_rens_scope_idren. } *)
  (*   { rewrite -IHS. f_equiv. clear. *)
  (*     intros v. dependent elimination v; *)
  (*       unfold hd_sub, tl_sub; simp subs_lift; auto. } *)
  (* Qed. *)

  (* Lemma interp_subs_scope_idsub {S} (env : interp_scope S) : *)
  (*   interp_subs_scope env idsub ≡ env. *)
  (* Proof. *)
  (*   induction S as [|[] S]; simp interp_subs_scope. *)
  (*   { by destruct env. } *)
  (*   destruct env as [x env]. *)
  (*   unfold hd_sub, idsub. simpl. *)
  (*   simp interp_var. simpl. f_equiv. *)
  (*   etrans; last first. *)
  (*   { apply IHS. } *)
  (*   rewrite -(interp_subs_scope_tl_sub x env idsub). *)
  (*   repeat f_equiv. intro v. unfold tl_sub, idsub; simpl. *)
  (*   simp subs_lift. unfold expr_lift. simp ren_expr. done. *)
  (* Qed. *)

  (* Lemma interp_expr_subst {S D : scope} (M : expr S) (s : subs S D) : *)
  (*   ∀ (E : interp_scope D), *)
  (*     interp_expr (subst_expr M s) E ≡ interp_expr M (interp_subs_scope E s) *)
  (* with interp_val_subst {S D : scope} (v : val S) (s : subs S D) : *)
  (*   ∀ (E : interp_scope D), *)
  (*     interp_val (subst_val v s) E ≡ interp_val v (interp_subs_scope E s). *)
  (* Proof. *)
  (*   - revert D s. induction M=> D r D2; simpl; simp subst_expr. *)
  (*     all: try by (simpl; repeat intro; simpl; repeat f_equiv; eauto). *)
  (*     + (* variable *) revert r. *)
  (*       induction v=>r. *)
  (*       * simp interp_var interp_rens_scope. done. *)
  (*       * simp interp_var interp_rens_scope. simpl. *)
  (*         apply (IHv (tl_sub r)). *)
  (*     + (* recursive functions *) simpl. *)
  (*       apply bi.siProp.internal_eq_soundness. *)
  (*       iLöb as "IH". *)
  (*       rewrite {2}interp_rec_unfold. *)
  (*       rewrite {2}(interp_rec_unfold (interp_expr M)). *)
  (*       iApply f_equivI. iNext. iApply internal_eq_pointwise. *)
  (*       rewrite /ir_unf. iIntros (x). simpl. *)
  (*       rewrite interp_expr_subst. *)
  (*       iApply f_equivI. *)
  (*       simp interp_subs_scope interp_var. simpl. *)
  (*       rewrite !interp_subs_scope_tl_sub. *)
  (*       iRewrite "IH". *)
  (*       done. *)
  (*   - revert D s. induction v=> D r D2; simpl; simp subst_val; eauto. *)
  (*     (* recursive functions *) *)
  (*     simp subst_expr. simpl. *)
  (*     apply bi.siProp.internal_eq_soundness. *)
  (*     iLöb as "IH". *)
  (*     rewrite {2}interp_rec_unfold. *)
  (*     rewrite {2}(interp_rec_unfold (interp_expr e)). *)
  (*     iApply f_equivI. iNext. iApply internal_eq_pointwise. *)
  (*     rewrite /ir_unf. iIntros (x). simpl. *)
  (*     rewrite interp_expr_subst. *)
  (*     iApply f_equivI. *)
  (*     simp interp_subs_scope interp_var. simpl. *)
  (*     rewrite !interp_subs_scope_tl_sub. *)
  (*     iRewrite "IH". *)
  (*     done. *)
  (* Qed. *)

  (* (** ** Interpretation is a homomorphism *) *)
  (* #[global] Instance interp_ectx_item_hom {S} (Ki : ectx_item S) env : *)
  (*   IT_hom (interp_ctx_item Ki env). *)
  (* Proof. destruct Ki; simpl; apply _. Qed. *)
  (* #[global] Instance interp_ectx_hom {S} (K : ectx S) env : *)
  (*   IT_hom (interp_ectx K env). *)
  (* Proof. induction K; simpl; apply _. Qed. *)

  (* (** ** Finally, preservation of reductions *) *)
  (* Lemma interp_expr_head_step {S} env (e : expr S) e' σ σ' n : *)
  (*   head_step e σ e' σ' (n,0) → *)
  (*   interp_expr e env ≡ Tick_n n $ interp_expr e' env. *)
  (* Proof. *)
  (*   inversion 1; cbn-[IF APP' INPUT Tick get_ret2]. *)
  (*   - (*fun->val*) *)
  (*     reflexivity. *)
  (*   - (* app lemma *) *)
  (*     rewrite APP_APP'_ITV. *)
  (*     trans (APP (Fun (Next (ir_unf (interp_expr e1) env))) (Next $ interp_val v2 env)). *)
  (*     { repeat f_equiv. apply interp_rec_unfold. } *)
  (*     rewrite APP_Fun. simpl. rewrite Tick_eq. do 2 f_equiv. *)
  (*     simplify_eq. *)
  (*     rewrite interp_expr_subst. f_equiv. *)
  (*     simp interp_subs_scope. unfold hd_sub, tl_sub. simp conssub. *)
  (*     simpl. repeat f_equiv. *)
  (*     generalize (Val (RecV e1)). *)
  (*     generalize (Val v2). *)
  (*     clear. *)
  (*     intros e1 e2. *)
  (*     trans (interp_subs_scope env idsub); last first. *)
  (*     {  f_equiv. intro v. simp conssub. done. } *)
  (*     symmetry. *)
  (*     apply interp_subs_scope_idsub. *)
  (*   - (* the natop stuff *) *)
  (*     simplify_eq. *)
  (*     destruct v1,v2; try naive_solver. simpl in *. *)
  (*     rewrite NATOP_Ret. *)
  (*     destruct op; simplify_eq/=; done. *)
  (*   - by rewrite IF_True. *)
  (*   - rewrite IF_False; eauto. lia. *)
  (* Qed. *)

  (* Lemma interp_expr_fill_no_reify {S} K env (e e' : expr S) σ σ' n : *)
  (*   head_step e σ e' σ' (n,0) → *)
  (*   interp_expr (fill K e) env ≡ Tick_n n $ interp_expr (fill K e') env. *)
  (* Proof. *)
  (*   intros He. *)
  (*   trans (interp_ectx K env (interp_expr e env)). *)
  (*   { apply interp_ectx_fill. } *)
  (*   trans (interp_ectx K env (Tick_n n (interp_expr e' env))). *)
  (*   {  f_equiv. apply (interp_expr_head_step env) in He. apply He. } *)
  (*   trans (Tick_n n $ interp_ectx K env (interp_expr e' env)); last first. *)
  (*   { f_equiv. symmetry. apply interp_ectx_fill. } *)
  (*   apply hom_tick_n. apply _. *)
  (* Qed. *)

  (* Opaque INPUT OUTPUT_. *)
  (* Opaque Ret. *)

  (* Lemma interp_expr_fill_yes_reify {S} K env (e e' : expr S) *)
  (*   (σ σ' : stateO) (σr : gState_rest sR_idx rs ♯ IT) n : *)
  (*   head_step e σ e' σ' (n,1) → *)
  (*   reify (gReifiers_sReifier rs) *)
  (*     (interp_expr (fill K e) env)  (gState_recomp σr (sR_state σ)) *)
  (*     ≡ (gState_recomp σr (sR_state σ'), Tick_n n $ interp_expr (fill K e') env). *)
  (* Proof. *)
  (*   intros Hst. *)
  (*   trans (reify (gReifiers_sReifier rs) (interp_ectx K env (interp_expr e env)) *)
  (*            (gState_recomp σr (sR_state σ))). *)
  (*   { f_equiv. by rewrite interp_ectx_fill. } *)
  (*   inversion Hst; simplify_eq; cbn-[gState_recomp]. *)
  (*   - trans (reify (gReifiers_sReifier rs) (INPUT (interp_ectx K env ◎ Ret)) (gState_recomp σr (sR_state σ))). *)
  (*     { repeat f_equiv; eauto. *)
  (*       rewrite hom_INPUT. f_equiv. by intro. } *)
  (*     rewrite reify_vis_eq //; last first. *)
  (*     { rewrite subReifier_reify/=//. *)
  (*       rewrite H4. done. } *)
  (*     repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv. *)
  (*     rewrite interp_ectx_fill. *)
  (*     by rewrite ofe_iso_21. *)
  (*   - trans (reify (gReifiers_sReifier rs) (interp_ectx K env (OUTPUT n0)) (gState_recomp σr (sR_state σ))). *)
  (*     { do 3 f_equiv; eauto. *)
  (*       rewrite get_ret_ret//. } *)
  (*     trans (reify (gReifiers_sReifier rs) (OUTPUT_ n0 (interp_ectx K env (Ret 0))) (gState_recomp σr (sR_state σ))). *)
  (*     { do 2 f_equiv; eauto. *)
  (*       rewrite hom_OUTPUT_//. } *)
  (*     rewrite reify_vis_eq //; last first. *)
  (*     { rewrite subReifier_reify/=//. } *)
  (*     repeat f_equiv. rewrite Tick_eq/=. repeat f_equiv. *)
  (*     rewrite interp_ectx_fill. *)
  (*     simpl. done. *)
  (* Qed. *)

  (* Lemma soundness {S} (e1 e2 : expr S) σ1 σ2 (σr : gState_rest sR_idx rs ♯ IT) n m env : *)
  (*   prim_step e1 σ1 e2 σ2 (n,m) → *)
  (*   ssteps (gReifiers_sReifier rs) *)
  (*             (interp_expr e1 env) (gState_recomp σr (sR_state σ1)) *)
  (*             (interp_expr e2 env) (gState_recomp σr (sR_state σ2)) n. *)
  (* Proof. *)
  (*   Opaque gState_decomp gState_recomp. *)
  (*   inversion 1; simplify_eq/=. *)
  (*   destruct (head_step_io_01 _ _ _ _ _ _ H2); subst. *)
  (*   - assert (σ1 = σ2) as ->. *)
  (*     { eapply head_step_no_io; eauto. } *)
  (*     eapply (interp_expr_fill_no_reify K) in H2. *)
  (*     rewrite H2. eapply ssteps_tick_n. *)
  (*   - inversion H2;subst. *)
  (*     + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2. *)
  (*       rewrite interp_ectx_fill. *)
  (*       rewrite hom_INPUT. *)
  (*       change 1 with (1+0). econstructor; last first. *)
  (*       { apply ssteps_zero; reflexivity. } *)
  (*       eapply sstep_reify. *)
  (*       { Transparent INPUT. unfold INPUT. simpl. *)
  (*         f_equiv. reflexivity. } *)
  (*       simpl in H2. *)
  (*       rewrite -H2. *)
  (*       repeat f_equiv; eauto. *)
  (*       rewrite interp_ectx_fill hom_INPUT. *)
  (*       eauto. *)
  (*     + eapply (interp_expr_fill_yes_reify K env _ _ _ _ σr) in H2. *)
  (*       rewrite interp_ectx_fill. simpl. *)
  (*       rewrite get_ret_ret. *)
  (*       rewrite hom_OUTPUT_. *)
  (*       change 1 with (1+0). econstructor; last first. *)
  (*       { apply ssteps_zero; reflexivity. } *)
  (*       eapply sstep_reify. *)
  (*       { Transparent OUTPUT_. unfold OUTPUT_. simpl. *)
  (*         f_equiv. reflexivity. } *)
  (*       simpl in H2. *)
  (*       rewrite -H2. *)
  (*       repeat f_equiv; eauto. *)
  (*       Opaque OUTPUT_. *)
  (*       rewrite interp_ectx_fill /= get_ret_ret hom_OUTPUT_. *)
  (*       eauto. *)
  (* Qed. *)

End interp.
#[global] Opaque INPUT OUTPUT_.
