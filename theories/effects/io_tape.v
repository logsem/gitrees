(** * I/O on a tape effect *)
From gitrees Require Import prelude gitree.

Record state := State {
                   inputs : list nat;
                   outputs : list nat;
                 }.
#[export] Instance state_inhabited : Inhabited state := populate (State [] []).

Definition update_input (s : state) : nat * state :=
  match s.(inputs) with
  | [] => (0, s)
  | n::ns =>
      (n, {| inputs := ns; outputs := s.(outputs) |})
  end.
Definition update_output (n:nat) (s : state) : state :=
  {| inputs := s.(inputs); outputs := n::s.(outputs) |}.

Notation stateO := (leibnizO state).

Program Definition inputE : opInterp :=
  {|
    Ins := unitO;
    Outs := natO;
  |}.

Program Definition outputE : opInterp :=
  {|
    Ins := natO;
    Outs := unitO;
  |}.

Definition ioE := @[inputE;outputE].

(* INPUT *)
Definition reify_input X `{Cofe X} : unitO * stateO →
                                      option (natO * stateO) :=
    λ '(o, σ), Some (update_input σ : prodO natO stateO).
#[export] Instance reify_input_ne X `{Cofe X} :
  NonExpansive (reify_input X).
Proof.
  intros ?[[]][[]][_?]. simpl in *. f_equiv.
  repeat f_equiv. done.
Qed.

(* OUTPUT *)
Definition reify_output X `{Cofe X} : (natO * stateO) →
                                       option (unitO * stateO) :=
  λ '(n, σ), Some((), update_output n σ : stateO).
#[export] Instance reify_output_ne X `{Cofe X} :
  NonExpansive (reify_output X).
Proof.
  intros ?[][][]. simpl in *.
  repeat f_equiv; done.
Qed.

Canonical Structure reify_io : sReifier NotCtxDep.
Proof.
  simple refine {| sReifier_ops := ioE;
                   sReifier_state := stateO
                |}.
  intros X HX op.
  destruct op as [[] | [ | []]]; simpl.
  - simple refine (OfeMor (reify_input X)).
  - simple refine (OfeMor (reify_output X)).
Defined.

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

End constructors.

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers NotCtxDep sz).
  Context {subR : subReifier reify_io rs}.
  Notation F := (gReifiers_ops rs).
  Context {R} `{!Cofe R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!invGS Σ, !stateG rs R Σ}.
  Notation iProp := (iProp Σ).

  Lemma wp_input (σ σ' : stateO) (n : nat) (k : natO -n> IT) Φ s :
    update_input σ = (n, σ') →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} (k n) @ s {{ Φ }}) -∗
    WP@{rs} (INPUT k) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold INPUT. simpl.
    iApply (wp_subreify_ctx_indep with "Hs").
    { simpl. rewrite Hs//=. }
    { simpl. by rewrite ofe_iso_21. }
    iModIntro. done.
  Qed.

  Lemma wp_output (σ σ' : stateO) (n : nat) Φ s :
    update_output n σ = σ' →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ' -∗ Φ (RetV 0)) -∗
    WP@{rs} (OUTPUT n) @ s {{ Φ }}.
  Proof.
    intros Hs. iIntros "Hs Ha".
    unfold OUTPUT. simpl.
    iApply (wp_subreify_ctx_indep rs with "Hs").
    { simpl. by rewrite Hs. }
    { simpl. done. }
    iModIntro. iIntros "H1 H2".
    iApply wp_val. by iApply ("Ha" with "H1 H2").
  Qed.

End weakestpre.
