(** * Representation of delimited continuations

This representation is inspired by the abstract machine semantics for
the CPS hierarchy, and is designed with manipualtion of
meta-continuations in mind.

We consider shift/reset, appcont operations, as well as the explicit
"pop" operation. The "state" for delimited continuations is a
meta-continuation: a stack of continuations corresponding to different
delimiters. Every time we do "reset" we push the current continuation
onto the stack, thus making the contiuation outside "reset" not
visible to the operations inside it. The "shift" operation behaves
similarly to call/cc by capturing the current continuation (which was
already delimited by reset). Finally, when we exit the scope of reset,
we need to restore the previous continuation which was pushed onto the
stack. For this, we explicitly use the "pop" operation.

 *)
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

(** Bind the innermost continuation *)
Program Definition shiftE : opInterp :=
  {|
    Ins := ((▶ ∙ -n> ▶ ∙) -n> ▶ ∙);
    Outs := (▶ ∙);
  |}.

(** Delimit the continuation *)
Program Definition resetE : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := (▶ ∙);
  |}.

(** Explicitly pop a continuation from the meta-continuation and jump
to it *)
Program Definition popE : opInterp :=
  {|
    Ins := (▶ ∙);
    Outs := Empty_setO;
  |}.

(** Applies continuation, pushes outer context in meta *)
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

Canonical Structure reify_delim : sReifier CtxDep.
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
    laterO_map 𝒫 (f (laterO_map k)) ≡ Next β →
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} β @ s {{ Φ }}) -∗
    WP@{rs} (k (SHIFT f)) @ s {{ Φ }}.
  Proof.
    iIntros (Hp) "Hs Ha".
    unfold SHIFT. simpl.
    rewrite hom_vis.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ (laterO_map 𝒫 $ f (laterO_map k)) with "Hs").
    {
      simpl. do 2 f_equiv; last done. do 2 f_equiv.
      rewrite ccompose_id_l. intro. simpl. by rewrite ofe_iso_21.
    }
    { exact Hp. }
    iModIntro.
    iApply "Ha".
  Qed.

  Lemma wp_reset (σ : state) (e : IT) (k : IT -n> IT) {Hk : IT_hom k}
    Φ s :
    has_substate σ -∗
    ▷ (£ 1 -∗ has_substate ((laterO_map k) :: σ) -∗
       WP@{rs} 𝒫 e @ s {{ Φ }}) -∗
    WP@{rs} k $ (RESET (Next e)) @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    unfold RESET. simpl. rewrite hom_vis.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ (Next $ 𝒫 e) with "Hs").
    - simpl. repeat f_equiv. rewrite ccompose_id_l.
      trans ((laterO_map k) :: σ); last reflexivity.
      f_equiv. intro. simpl. by rewrite ofe_iso_21.
    - reflexivity.
    - iApply "Ha".
  Qed.

  Lemma wp_pop_end (v : IT)
    {HV : AsVal v}
    Φ s :
    has_substate [] -∗
    ▷ (£ 1 -∗ has_substate [] -∗ WP@{rs} v @ s {{ Φ }}) -∗
    WP@{rs} 𝒫 v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((Next v)) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  Lemma wp_pop_cons (σ : state) (v : IT) (k : IT -n> IT)
    {HV : AsVal v}
    Φ s :
    has_substate ((laterO_map k) :: σ) -∗
    ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k $ v @ s {{ Φ }}) -∗
    WP@{rs} 𝒫 v @ s {{ Φ }}.
  Proof.
    iIntros "Hs Ha".
    rewrite get_val_ITV. simpl.
    iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ ((laterO_map k (Next v))) with "Hs").
    - simpl. reflexivity.
    - reflexivity.
    - done.
  Qed.

  (* Lemma wp_get_val (α : IT) (f : IT -n> IT) *)
  (*   Φ `{!NonExpansive Φ} s : *)
  (*   WP@{rs} α @ s {{ βv, WP@{rs} (f (IT_of_V βv)) @ s {{ Φ }} }} *)
  (*   -∗ WP@{rs} get_val f α @ s {{ Φ }}. *)
  (* Proof. *)
  (*   iLöb as "IH" forall ( α ). *)
  (*   iIntros "Ha". *)
  (*   destruct (IT_dont_confuse α) *)
  (*     as [[e ->] | [[m ->] | [ [g ->] | [[α' ->]|[op [i [ko ->]]]] ]]]. *)
  (*   - rewrite get_val_err. *)
  (*     rewrite ->wp_unfold at 1. *)
  (*     iDestruct "Ha" as "[Ha | Ha]". *)
  (*     + iDestruct "Ha" as "(%αv & Ha & _)". *)
  (*       rewrite IT_to_V_Err. *)
  (*       by iPoseProof (option_equivI with "Ha") as "Ha". *)
  (*     + iDestruct "Ha" as "(H1 & H2)". *)
  (*       iEval (rewrite wp_unfold). *)
  (*       iRight. *)
  (*       iSplit; first done. *)
  (*       iIntros (σ) "Hσ". *)
  (*       iSpecialize ("H2" $! σ with "Hσ"). *)
  (*       iMod "H2". *)
  (*       iDestruct "H2" as "(H2 & H3)". *)
  (*       iDestruct "H2" as "[H2 | H2]". *)
  (*       * iDestruct "H2" as "(%α' & %σ' & H2)". *)
  (*         iExFalso. *)
  (*         by iDestruct (istep_err with "H2") as "H2". *)
  (*       * iDestruct "H2" as "(%err & HEQ & H2)". *)
  (*         iDestruct (Err_inj' with "HEQ") as "%HEQ". *)
  (*         rewrite HEQ. *)
  (*         iModIntro. *)
  (*         iSplit. *)
  (*         -- iRight. *)
  (*            iExists err. *)
  (*            iSplit; done. *)
  (*         -- iIntros (σ' β) "Hst Hc". *)
  (*            iExFalso. *)
  (*            iDestruct "Hst" as "[(Hst & _) | (%op & %i & %k & Hst & _)]". *)
  (*            ++ iDestruct (internal_eq_sym with "Hst") as "Hst". *)
  (*               by iDestruct (IT_tau_err_ne with "Hst") as "Hst". *)
  (*            ++ iDestruct (internal_eq_sym with "Hst") as "Hst". *)
  (*               by iDestruct (IT_vis_err_ne with "Hst") as "Hst". *)
  (*   - rewrite core.get_val_ret. *)
  (*     iDestruct (wp_val_inv with "Ha") as "Ha"; *)
  (*       first solve_proper. *)
  (*     by iApply fupd_wp. *)
  (*   - rewrite get_val_fun. *)
  (*     iDestruct (wp_val_inv with "Ha") as "Ha"; *)
  (*       first solve_proper. *)
  (*     by iApply fupd_wp. *)
  (*   - rewrite get_val_tick. *)
  (*     rewrite ->wp_unfold at 1. *)
  (*     iDestruct "Ha" as "[Ha | Ha]". *)
  (*     + iDestruct "Ha" as "(%αv & Ha & _)". *)
  (*       rewrite IT_to_V_Tick. *)
  (*       by iPoseProof (option_equivI with "Ha") as "Ha". *)
  (*     + iDestruct "Ha" as "(H1 & H2)". *)
  (*       iEval (rewrite wp_unfold). *)
  (*       iRight. *)
  (*       iSplit. *)
  (*       { *)
  (*         iClear "∗". rewrite IT_to_V_Tick. *)
  (*         done. *)
  (*       } *)
  (*       iIntros (σ) "Hσ". *)
  (*       iSpecialize ("H2" $! σ with "Hσ"). *)
  (*       iMod "H2". *)
  (*       iDestruct "H2" as "(H2 & H3)". *)
  (*       iDestruct "H2" as "[H2 | H2]". *)
  (*       * iDestruct "H2" as "(%α'' & %σ' & #H2)". *)
  (*         iSpecialize ("H3" $! σ' α'' with "H2"). *)
  (*         iModIntro. *)
  (*         iSplit. *)
  (*         -- iLeft. *)
  (*            iExists (get_val f α'). *)
  (*            iExists σ. *)
  (*            iLeft. *)
  (*            iSplit; done. *)
  (*         -- iIntros (σ'' α''') "#H4 Hc". *)
  (*            iSpecialize ("H3" with "Hc"). *)
  (*            iMod "H3". *)
  (*            iModIntro. *)
  (*            iNext. *)
  (*            iMod "H3". *)
  (*            iModIntro. *)
  (*            iMod "H3". *)
  (*            iModIntro. *)
  (*            iDestruct "H4" as "[H4 | H4]". *)
  (*            ++ iDestruct "H4" as "(HEQ1 & HEQ2)". *)
  (*               iRewrite -"HEQ1". *)
  (*               iRewrite -"HEQ2". *)
  (*               iClear "HEQ1 HEQ2". *)
  (*               iDestruct "H2" as "[H2 | H2]". *)
  (*               ** iDestruct "H2" as "(HEQ1 & HEQ2)". *)
  (*                  iRewrite "HEQ1". *)
  (*                  iRewrite "HEQ2". *)
  (*                  iClear "HEQ1 HEQ2". *)
  (*                  iDestruct "H3" as "($ & H3)". *)
  (*                  by iApply "IH". *)
  (*               ** iDestruct "H2" as "(%op & %i & %k & Hst & _)". *)
  (*                  iExFalso. *)
  (*                  by iDestruct (IT_tau_vis_ne with "Hst") as "Hst'". *)
  (*            ++ iDestruct "H4" as "(%op & %i & %k & Hst & _)". *)
  (*               iExFalso. *)
  (*               by iDestruct (IT_tau_vis_ne with "Hst") as "Hst'". *)
  (*       * iDestruct "H2" as "(%err & HEQ & H2)". *)
  (*         by iDestruct (IT_tau_err_ne with "HEQ") as "HEQ". *)
  (*   - rewrite get_val_vis. *)
  (*     iClear "IH". *)
  (*     rewrite ->wp_unfold at 1. *)
  (*     iDestruct "Ha" as "[Ha | Ha]". *)
  (*     + iDestruct "Ha" as "(%αv & Ha & _)". *)
  (*       rewrite IT_to_V_Vis. *)
  (*       by iPoseProof (option_equivI with "Ha") as "Ha". *)
  (*     + iDestruct "Ha" as "(H1 & H2)". *)
  (*       iEval (rewrite wp_unfold). *)
  (*       iRight. *)
  (*       iSplit. *)
  (*       { *)
  (*         iClear "∗". rewrite IT_to_V_Vis. *)
  (*         done. *)
  (*       } *)
  (*       iIntros (σ) "Hσ". *)
  (*       iSpecialize ("H2" $! σ with "Hσ"). *)
  (*       iMod "H2". *)
  (*       iDestruct "H2" as "(H2 & H3)". *)
  (*       iDestruct "H2" as "[H2 | H2]". *)
  (*       * iDestruct "H2" as "(%α'' & %σ' & #H2)". *)
  (*         iModIntro. *)
  (*         iSplit. *)
  (*         -- iLeft. *)
  (*            admit. *)
  (*         -- iIntros (σ'' β) "Hst Hc". *)
  (*            iSpecialize ("H3" $! σ' β). *)
  (*            admit. *)
  (*       * iDestruct "H2" as "(%err & HEQ & H2)". *)
  (*         by iDestruct (IT_vis_err_ne with "HEQ") as "HEQ". *)
  (* Admitted.         *)

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
