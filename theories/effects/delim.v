From gitrees Require Import prelude gitree.
From iris.algebra Require Import list.

(** * State, corresponding to a meta-continuation *)
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
Program Definition pop_apply_E : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := Empty_setO;
  |}.

Program Definition peek_apply_E : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := Empty_setO;
  |}.

Program Definition pop_continue_E : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := (▶ ∙);
  |}.

Program Definition pop_discard_E : opInterp :=
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

Program Definition shiftE' : opInterp :=
  {|
    Ins := ((▶ ∙ -n> ▶ ∙) -n> ▶ ∙);
    Outs := (▶ ∙);
  |}.

Definition delimE := @[shiftE
                       ; resetE
                       ; pop_apply_E
                       ; peek_apply_E
                       ; pop_continue_E
                       ; pop_discard_E
                       ; appContE
                       ; shiftE'].

Notation op_shift        := (inl ()).
Notation op_reset        := (inr (inl ())).
Notation op_pop_apply    := (inr (inr (inl ()))).
Notation op_peek_apply   := (inr (inr (inr (inl ())))).
Notation op_pop_continue := (inr (inr (inr (inr (inl ()))))).
Notation op_pop_discard  := (inr (inr (inr (inr (inr (inl ())))))).
Notation op_app_cont     := (inr (inr (inr (inr (inr (inr (inl ()))))))).
Notation op_shift'       := (inr (inr (inr (inr (inr (inr (inr (inl ())))))))).

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

  Definition reify_pop_apply : (laterO X) * state * (Empty_setO -n> laterO X) →
                               option (laterO X * state) :=
    λ '(e, σ, _),
      match σ with
      | [] => Some (e, σ)
      | k' :: σ' => Some (k' e, σ')
      end.
  #[export] Instance reify_pop_apply_ne :
    NonExpansive (reify_pop_apply :
        prodO (prodO (laterO X) state) (Empty_setO -n> laterO X) →
        optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. by repeat f_equiv. Qed.

  Definition reify_peek_apply : (laterO X) * state * (Empty_setO -n> laterO X) →
                           option (laterO X * state) :=
    λ '(e, σ, _),
      match σ with
      | [] => Some (e, σ)
      | k' :: σ' => Some (k' e, k' :: σ')
      end.
  #[export] Instance reify_peek_apply_ne :
    NonExpansive (reify_peek_apply :
        prodO (prodO (laterO X) state) (Empty_setO -n> laterO X) →
        optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. by repeat f_equiv. Qed.

  Definition reify_pop_continue : (laterO X) * state * (laterO X -n> laterO X) →
                                  option (laterO X * state) :=
    λ '(e, σ, κ),
      match σ with
      | [] => Some (κ e, σ)
      | _ :: σ' => Some (κ e, σ')
      end.
  #[export] Instance reify_pop_continue_ne :
    NonExpansive (reify_pop_continue :
        prodO (prodO (laterO X) state) (laterO X -n> laterO X) →
        optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. by repeat f_equiv. Qed.

  Definition reify_pop_discard : (laterO X) * state * (Empty_setO -n> laterO X) →
                                 option (laterO X * state) :=
    λ '(e, σ, _),
      match σ with
      | [] => Some (e, σ)
      | _ :: σ' => Some (e, σ')
      end.
  #[export] Instance reify_pop_discard_ne :
    NonExpansive (reify_pop_discard :
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

  Definition reify_shift' : ((laterO X -n> laterO X) -n> laterO X) *
                              state * (laterO X -n> laterO X) →
                            option (laterO X * state) :=
    λ '(f, σ, k), Some ((f k): laterO X, tail (σ : state)).
  #[export] Instance reify_shift_ne' :
    NonExpansive (reify_shift' :
      prodO (prodO ((laterO X -n> laterO X) -n> laterO X) state)
        (laterO X -n> laterO X) →
      optionO (prodO (laterO X) state)).
  Proof. intros ?[[]][[]][[]]. simpl in *. repeat f_equiv; auto. Qed.

End reifiers.

Canonical Structure reify_delim : sReifier CtxDep.
Proof.
  simple refine {|
             sReifier_ops := delimE;
             sReifier_state := stateF
           |}.
  intros X HX op.
  destruct op as [ | [ | [ | [| [| [| [| [| []]]]]]]]]; simpl.
  - simple refine (OfeMor (reify_shift)).
  - simple refine (OfeMor (reify_reset)).
  - simple refine (OfeMor (reify_pop_apply)).
  - simple refine (OfeMor (reify_peek_apply)).
  - simple refine (OfeMor (reify_pop_continue)).
  - simple refine (OfeMor (reify_pop_discard)).
  - simple refine (OfeMor (reify_app_cont)).
  - simple refine (OfeMor (reify_shift')).
Defined.

Section constructors.
  Context {E : opsInterp} {A} `{!Cofe A}.
  Context {subEff0 : subEff delimE E}.
  Context {subOfe0 : SubOfe natO A}.
  Context {subOfe1 : SubOfe unitO A}.
  Notation IT := (IT E A).
  Notation ITV := (ITV E A).

  (** ** POP *)

  Program Definition POP_APPLY : IT -n> IT :=
    λne e, Vis (E:=E) (subEff_opid op_pop_apply)
             (subEff_ins (F:=delimE) (op:=op_pop_apply) (Next e))
             (Empty_setO_rec _ ◎ (subEff_outs (F:=delimE) (op:=op_pop_apply))^-1).
  Solve All Obligations with solve_proper.

  Program Definition PEEK_APPLY : IT -n> IT :=
    λne e, Vis (E:=E) (subEff_opid op_peek_apply)
             (subEff_ins (F:=delimE) (op:=op_peek_apply) (Next e))
             (Empty_setO_rec _ ◎ (subEff_outs (F:=delimE) (op:=op_peek_apply))^-1).
  Solve All Obligations with solve_proper.

  Program Definition POP_CONTINUE_ : (IT -n> IT) -n> IT -n> IT :=
    λne k e, Vis (E:=E) (subEff_opid op_pop_continue)
             (subEff_ins (F:=delimE) (op:=op_pop_continue) (Next e))
             (laterO_map k ◎ (subEff_outs (F:=delimE) (op:=op_pop_continue))^-1).
  Solve All Obligations with solve_proper.

  Program Definition POP_CONTINUE : IT -n> IT :=
    POP_CONTINUE_ idfun.

  Program Definition POP_DISCARD : IT -n> IT :=
    λne e, Vis (E:=E) (subEff_opid op_pop_discard)
             (subEff_ins (F:=delimE) (op:=op_pop_discard) (Next e))
             (Empty_setO_rec _ ◎ (subEff_outs (F:=delimE) (op:=op_pop_discard))^-1).
  Solve All Obligations with solve_proper.

  Notation 𝒫 := (get_val POP_APPLY).
  Notation ℛ := (get_val PEEK_APPLY).
  Notation 𝒞 := (get_val POP_CONTINUE).
  Notation ℱ := (get_val POP_DISCARD).

  (** ** RESET *)

  Program Definition RESET_ : (laterO IT -n> laterO IT) -n>
                                laterO IT -n>
                                IT :=
    λne k e, Vis (E:=E) (subEff_opid op_reset)
               (subEff_ins (F := delimE) (op := op_reset) e)
               (k ◎ subEff_outs (F := delimE) (op := op_reset)^-1).
  Solve Obligations with solve_proper.

  Program Definition RESET : laterO IT -n> IT :=
    RESET_ idfun.

  (** ** SHIFT *)

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

Notation 𝒫 := (get_val POP_APPLY).
Notation ℛ := (get_val PEEK_APPLY).
Notation 𝒞 := (get_val POP_CONTINUE).
Notation ℱ := (get_val POP_DISCARD).

Section weakestpre.
  Context {sz : nat}.
  Variable (rs : gReifiers CtxDep sz).
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
    (k : IT -n> IT) β {Hk : IT_hom k} Φ s :
    (f (laterO_map k)) ≡ Next β →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} β @ s {{ Φ }}) -∗
    WP@{rs} (k (SHIFT f)) @ s {{ Φ }}.
  Proof.
    iIntros (Hp) "Hs Ha".
    unfold SHIFT. simpl.
    rewrite hom_vis.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ (f (laterO_map k)) with "Hs").
    {
      simpl. do 2 f_equiv; last done.
      rewrite ccompose_id_l.
      f_equiv.
      intros ?.
      simpl.
      rewrite ofe_iso_21.
      reflexivity.
    }
    { exact Hp. }
    iModIntro.
    iApply "Ha".
  Qed.

  Lemma wp_reset (σ : state) (e : IT) (k : IT -n> IT) {Hk : IT_hom k}
    Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗
       WP@{rs} e @ s {{ Φ }}) -∗
    WP@{rs} k $ (RESET (Next e)) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold RESET. simpl. rewrite hom_vis.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ (Next $ e) with "Hs").
    - simpl. repeat f_equiv. rewrite ccompose_id_l.
      trans ((laterO_map k) :: σ); last reflexivity.
      f_equiv. intro. simpl. by rewrite ofe_iso_21.
    - reflexivity.
    - iApply "Ha".
  Qed.

  Lemma wp_pop_apply_end (e : IT)
    Φ s :
    has_substate []
    -∗ ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} e @ s {{ Φ }})
    -∗ WP@{rs} POP_APPLY e @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next e)) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_pop_apply_cons (σ : state) (e : IT) (k : IT -n> IT)
    Φ s :
    has_substate ((laterO_map k) :: σ)
    -∗ ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k $ e @ s {{ Φ }})
    -∗ WP@{rs} POP_APPLY e @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((laterO_map k (Next e))) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_peek_apply_end (e : IT)
    Φ s :
    has_substate []
    -∗ ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} e @ s {{ Φ }})
    -∗ WP@{rs} PEEK_APPLY e @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next e)) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_peek_apply_cons (σ : state) (e : IT) (k : IT -n> IT)
    Φ s :
    has_substate ((laterO_map k) :: σ)
    -∗ ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗ WP@{rs} k $ e @ s {{ Φ }})
    -∗ WP@{rs} PEEK_APPLY e @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((laterO_map k (Next e))) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_pop_continue (e : IT) σ
    Φ s :
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate (tail σ) -∗ WP@{rs} e @ s {{ Φ }})
    -∗ WP@{rs} POP_CONTINUE e @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    destruct σ.
    - iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next e)) with "Hs").
      + simpl; rewrite ofe_iso_21 later_map_Next; reflexivity.
      + reflexivity.
      + done.
    - iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next e)) with "Hs").
      + simpl; rewrite ofe_iso_21 later_map_Next; reflexivity.
      + reflexivity.
      + done.
  Qed.

  Lemma wp_pop_discard (e : IT) σ
    Φ s :
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate (tail σ) -∗ WP@{rs} e @ s {{ Φ }})
    -∗ WP@{rs} POP_DISCARD e @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    destruct σ.
    - iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next e)) with "Hs").
      + simpl.
        reflexivity.
      + reflexivity.
      + done.
    - iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next e)) with "Hs").
      + simpl.
        reflexivity.
      + reflexivity.
      + done.
  Qed.

  Lemma wp_pop_apply_end' (v : IT)
    {HV : AsVal v}
    Φ s :
    has_substate []
    -∗ ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} v @ s {{ Φ }})
    -∗ WP@{rs} 𝒫 v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_pop_apply_end with "Hs Ha").
  Qed.

  Lemma wp_pop_apply_cons' (σ : state) (v : IT) (k : IT -n> IT)
    {HV : AsVal v}
    Φ s :
    has_substate ((laterO_map k) :: σ)
    -∗ ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k $ v @ s {{ Φ }})
    -∗ WP@{rs} 𝒫 v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_pop_apply_cons with "Hs Ha").
  Qed.

  Lemma wp_peek_apply_end' (v : IT)
    {HV : AsVal v}
    Φ s :
    has_substate []
    -∗ ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} v @ s {{ Φ }})
    -∗ WP@{rs} ℛ v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_peek_apply_end with "Hs Ha").
  Qed.

  Lemma wp_peek_apply_cons' (σ : state) (v : IT) (k : IT -n> IT)
    {HV : AsVal v}
    Φ s :
    has_substate ((laterO_map k) :: σ)
    -∗ ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗ WP@{rs} k $ v @ s {{ Φ }})
    -∗ WP@{rs} ℛ v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_peek_apply_cons with "Hs Ha").
  Qed.

  Lemma wp_pop_continue' (v : IT) σ
    {HV : AsVal v}
    Φ s :
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate (tail σ) -∗ WP@{rs} v @ s {{ Φ }})
    -∗ WP@{rs} 𝒞 v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_pop_continue with "Hs Ha").
  Qed.

  Lemma wp_pop_discard' (v : IT) σ
    {HV : AsVal v}
    Φ s :
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate (tail σ) -∗ WP@{rs} v @ s {{ Φ }})
    -∗ WP@{rs} ℱ v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_pop_discard with "Hs Ha").
  Qed.

  Lemma wp_app_cont (σ : state) (e : laterO IT) (k' : laterO (IT -n> IT))
    (k : IT -n> IT) β {Hk : IT_hom k}
    Φ s :
    laterO_ap k' e ≡ Next β →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗
       WP@{rs} β @ s {{ Φ }}) -∗
    WP@{rs} k (APP_CONT e k') @ s {{ Φ }}.
  Proof.
    iIntros (Hb) "Hs Ha".
    unfold APP_CONT. simpl. rewrite hom_vis.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ (Next β) with "Hs").
    - cbn-[laterO_ap]. rewrite Hb. do 2 f_equiv.
      trans (laterO_map k :: σ); last reflexivity.
      rewrite ccompose_id_l. f_equiv. intro. simpl. by rewrite ofe_iso_21.
    - reflexivity.
    - iApply "Ha".
  Qed.

End weakestpre.
