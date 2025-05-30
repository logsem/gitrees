From gitrees Require Import gitree.
From iris.algebra Require Import list.

Module Type ExcSig.
  Parameter E : Set.
  Parameter eq_dec_E : EqDecision E.
  Parameter countable_E : @Countable E eq_dec_E.
End ExcSig.

Module Exc (Errors : ExcSig).
  Import Errors.

  Structure exc := Exc { value : E }.
  
  #[global] Instance eq_dec : EqDecision exc.
    intros [x] [y].
    destruct (eq_dec_E x y) as [<-|HDiff].
    - left. reflexivity.
    - right. intros Heq. injection Heq as <-. apply HDiff. reflexivity.
  Defined.

  #[global] Instance countable_exc : Countable exc.
  Proof.
    refine (Build_Countable _ _ ?[encode] ?[decode] _).
    [encode] : { intros [e].
                 exact ((@encode _ _ countable_E) e).
    }
    [decode] : { intros p.
                 destruct ((@decode _ _ countable_E) p) as [e|].
                 - exact (Some (Exc e)).
                 - exact None.
    }
    intros [e].
    simpl.
    by rewrite (@decode_encode _ _ countable_E).
  Defined.
  
  Canonical Structure excO := leibnizO exc.
  Definition excOF := constOF exc.
  
  (** State functor, we keep track of the list of error handlers from most recently
      registered to least recently registered along with the error they each
      handle and the continuation present at the time of registration, this is      
      so that when  raising an error we can erase only the context between the    
      raising of the error and the registering of the handler **)
  Definition stateF : oFunctor := listOF (excOF * (▶ ∙ -n> ▶ ∙ ) * (▶ ∙ -n> ▶ ∙)).
  
  (** Register an exception handler for an exception type **)
  Program Definition regE : opInterp :=
    {|
      Ins := (excOF * (▶ ∙ -n> ▶ ∙ ) * (▶ ∙));
      Outs := (▶ ∙)
    |}.
  
  Program Definition popE : opInterp :=
    {|
      Ins := excOF;
      Outs := unitO
    |}.
  
  (** Throw an exception, empty Outs because we don't use the continuation **)
  Program Definition throwE : opInterp :=
    {|
      Ins := (excOF * (▶ ∙));
      Outs := Empty_setO;
    |}.
  
  Definition exceptE := @[regE;popE;throwE].
  
  (** Register a handler : Push the handler and current context on the stack **)
  Definition reify_reg X `{Cofe X} :
    excO * (laterO X -n> laterO X) * (laterO X)
    * (stateF ♯ X) * (laterO X -n> laterO X) →
    option (laterO X * (stateF ♯ X) * listO (laterO X)) :=
      λ '(e, h, b, σ, k), Some (b, (e,h,k)::σ, []).
  
  #[export] Instance reify_reg_ne X `{Cofe X}
    : NonExpansive (reify_reg X : excO * (laterO X -n> laterO X)
                                  * (laterO X) * (stateF ♯ X) * (laterO X -n> laterO X)
                                  → option (laterO X * (stateF ♯ X) * listO (laterO X))).
  Proof.
    solve_proper_prepare.
    destruct x as [[[[? ?] ?] ?] ?].
    destruct y as [[[[? ?] ?] ?] ?].
      repeat rewrite e pair_dist in H0.
      destruct H0 as [[[[? ?] ?] ?] ?].
      repeat f_equiv; done.
  Qed.
  
  (** Unregister a handler : Remove the topmost handler, restore the ambient context from when it was registered **)
  Definition reify_pop X `{Cofe X} :
    excO * (stateF ♯ X) * (unitO -n> laterO X)
    → option (laterO X * (stateF ♯ X) * listO (laterO X)) :=
    λ '(err, σ, k), match σ with
                    | [] => None
                    | (err', h, k')::σ' =>
                        (if (eq_dec err err')
                         then Some (k' (k ()), σ', [])
                         else None)
                    end.
  
  #[export] Instance reify_pop_ne X `{Cofe X} :
    NonExpansive (reify_pop X :
        excO * (stateF ♯ X) * (unitO -n> laterO X)
        → option (laterO X * (stateF ♯ X) * listO (laterO X))).
  Proof.
    intros n [[e σ] k] [[e' σ'] k'] Hequiv.
    rewrite pair_dist in Hequiv.
    destruct Hequiv as [[He Hσ] Hk].
    simpl in *.
    destruct σ' as [|p σ'].
    - rewrite nil_dist_eq in Hσ.
      rewrite Hσ. done.
    - apply cons_dist_eq in Hσ.
      destruct Hσ as (x & l' & Hx & Hl' & ->).
      destruct x as [[xerr xh] xc].
      destruct p as [[perr ph] pc].
      repeat rewrite pair_dist in Hx.
      destruct Hx as [[Herr Hh] Hc].
      rewrite He Herr.
      destruct (eq_dec e' perr).
      + rewrite Hl'. repeat f_equiv; done.
      + reflexivity.
  Qed.
  
  Fixpoint _cut_when {A : ofe} (p : (A -n> boolO)) (l : listO A) :
    optionO (A * listO A)%type :=
    match l with
    | [] => None
    | x::t => if p x then Some (x, t) else _cut_when p t
    end.
  
  Program Definition cut_when {A} : (A -n> boolO) -n> (listO A) -n> optionO (A * listO A)%type
    := λne p l, _cut_when p l.
  Next Obligation.
  Proof.
    solve_proper_prepare.
    generalize dependent y.
    induction x as [|h t IH].
    - intros y Hy.
      symmetry in Hy.
      apply nil_dist_eq in Hy.
      subst.
      done.
    - intros y Hy.
      symmetry in Hy.
      apply cons_dist_eq in Hy.
      destruct Hy as (h' & t' & Hh & Ht & ->).
      destruct (p h) eqn:Hp;
        rewrite -Hh in Hp;
        rewrite Hp.
      + repeat f_equiv; done.
      + apply IH. done.
  Qed.
  
  Next Obligation.
  Proof.
    solve_proper_prepare.
      induction x0 as [|h t IH].
    - done.
    - simpl.
      destruct H with h.
      destruct (x h).
      + done.
      + apply IH.
  Qed.
  
  Lemma cut_when_first_occ {A} : ∀ (p : A -n> bool) (l pre post : list A) (a : A),
    l = pre ++ a::post →
    p a = true →
    Forall (λ x,  p x = false) pre →
    cut_when p l = Some (a, post).
  Proof.
    intros p l pre post a Hl Ha Hpre.
    generalize dependent l.
    induction pre as [|h t].
    - intros l ->.
      simpl.
      rewrite Ha.
      exact eq_refl.
    - intros l ->.
      inversion Hpre as [|?? Hh Ht].
      simpl.
      rewrite Hh.
      apply IHt; done.
  Qed.
  
  Program Definition aux {X} (err : exc) : (excO * (laterO X -n> laterO X) * (laterO X -n> laterO X))%type -n> boolO :=
    λne '(err', _, _), if eq_dec err err' then true else false.
  Next Obligation.
  Proof.
    intros.
    simpl.
    intros [[e k] p] [[e' k'] p'] Heq.
    rewrite pair_dist in Heq.
    destruct Heq as [[He Hk] Hp].
    simpl in *.
    rewrite He.
    reflexivity.
  Qed.
  
  (** Raise an error : Find the most recent handler handling this error and remove all handlers registered after it from the stack then invoke the handler inside the context from when it was registered **)
  Definition reify_throw X `{Cofe X} :
    (excO * laterO X) * (stateF ♯ X) * (Empty_setO -n> laterO X)
    → option (laterO X * (stateF ♯ X) * listO (laterO X)) :=
    λ '(x, σ, _), let (err,v) := x in
                  match cut_when (aux err) σ with
                  | None => None
                  | Some (_, h, k, σ') => Some (k (h v), σ', [])
                  end.
  
  #[export] Instance reify_throw_ne X `{Cofe X} :
    NonExpansive (reify_throw X :
        (excO * laterO X) * (stateF ♯ X) * (Empty_setO -n> laterO X)
        → option (laterO X * (stateF ♯ X) * listO (laterO X))).
  Proof.
    solve_proper_prepare.
    destruct x as [[[e v] σ] k].
    destruct y as [[[e' v'] σ'] k'].
    destruct H0 as [[[He Hv] Hσ] Hk].
    simpl in *.
    generalize dependent σ'.
    induction σ as [|[[err hand] kont] σ].
    - intros.
      symmetry in Hσ.
      apply nil_dist_eq in Hσ.
      rewrite Hσ.
      done.
    - intros.
      symmetry in Hσ.
      apply cons_dist_eq in Hσ.
      destruct Hσ as ([[err' hand'] kont'] & σ'' & [[Herr Hhand] Hkont] & Hσ'' & ->).
      simpl in *.
      destruct (eq_dec e err) eqn:HEq.
      + rewrite Herr -He. rewrite HEq. repeat f_equiv; done.
      + symmetry in Hσ''.
        setoid_replace (if eq_dec e' err' then true else false) with (if eq_dec e err then true else false).
        * rewrite HEq.
          exact (IHσ σ'' Hσ'').
        * rewrite Herr -He. reflexivity.
  Qed.      
  
  Canonical Structure reify_exc : sReifier CtxDep.
  Proof.
    simple refine {| sReifier_ops := exceptE;
                      sReifier_state := stateF
                  |}.
    intros X HX op.
    destruct op as [|[|[|[]]]].
    - simple refine (OfeMor (reify_reg X)).
    - simple refine (OfeMor (reify_pop X)).
    - simple refine (OfeMor (reify_throw X)).
  Defined.
  
  Section constructors.
    Context {Eff : opsInterp} {A} `{!Cofe A}.
    Context {subEff0 : subEff exceptE Eff}.
    Context {SubOfe0 : SubOfe unitO A}.
    Notation IT := (IT Eff A).
    Notation ITV := (ITV Eff A).    
    
    Program Definition _REG : excO -n> (laterO IT -n> laterO IT) -n> laterO IT -n> IT :=
      λne e h b, Vis (E:=Eff) (subEff_opid (inl ()))
                   (subEff_ins (F:=exceptE) (op:=(inl ())) (e,h,b))
                   ((λne x, x) ◎ (subEff_outs (F:=exceptE) (op:=(inl ())))^-1).
    Solve All Obligations with solve_proper.

    
    Program Definition _POP : excO -n> IT :=
      λne e, Vis (E:=Eff) (subEff_opid (inr (inl ())))
               (subEff_ins (F:=exceptE) (op:=(inr(inl ()))) e)
               ((λne _, Next $ Ret ()) ◎ (subEff_outs (F:=exceptE) (op:=(inr(inl ()))))^-1).
    Solve All Obligations with solve_proper.
    
    Program Definition CATCH : excO -n> (laterO IT -n> laterO IT) -n> IT -n> IT :=
      λne err h b,
        _REG err h (Next $ get_val
                      (λne res, get_val
                                  (λne _, res)
                                  (_POP err)
                      ) b
          ).
    Next Obligation.
    Proof.
      solve_proper_prepare.
      done.
    Qed.
    Next Obligation.
      solve_proper_prepare.
      apply get_val_ne.
      solve_proper.
    Qed.
    Next Obligation.
      solve_proper.
    Qed.
    Next Obligation.
      solve_proper_prepare.
      repeat f_equiv.
      solve_proper.
    Qed.
    Next Obligation.
      solve_proper_prepare.
      repeat f_equiv; first done.
      apply get_val_ne.
      solve_proper.
    Qed.
    
    Program Definition _THROW : excO -n> laterO IT -n> IT :=
      λne e v,
        Vis (E:=Eff) (subEff_opid (inr (inr (inl ()))))
          (subEff_ins (F:=exceptE) (op:=(inr(inr(inl ())))) (e,v))
          (λne x, Empty_setO_rec _ ((subEff_outs (F:=exceptE) (op:=(inr(inr(inl ())))))^-1 x)).
    Next Obligation.
      solve_proper_prepare.
      destruct ((subEff_outs ^-1) x).
    Qed.
    Solve All Obligations with solve_proper.

    Program Definition THROW : excO -n> IT -n> IT :=
      λne e x,  get_val (λne res, _THROW e (Next res)) x.
    Next Obligation. Proof. solve_proper. Qed.
    Next Obligation. Proof. solve_proper. Qed.
    Next Obligation.
    Proof.
      solve_proper_prepare.
      apply get_val_ne.
      solve_proper.
    Qed.
    
  End constructors.
  
  Section weakestpre.
    
    Context {sz : nat}.
    Variable (rs : gReifiers CtxDep sz).
    Context {subR : subReifier reify_exc rs}.
    Notation F := (gReifiers_ops rs).
    Context {R} `{!Cofe R}.
    Context {SubOfe0 : SubOfe unitO R}.
    Context {SubOfe1 : SubOfe natO R}.
    Notation IT := (IT F R).
    Notation ITV := (ITV F R).
    Context `{!gitreeGS_gen rs R Σ}.
    Notation iProp := (iProp Σ).
    
    Lemma wp_reg (σ : stateF ♯ IT) (err : excO) (h : laterO IT -n> laterO IT) (k : IT -n> IT)
      {Hk : IT_hom k} b β s Φ :
      b ≡ Next β →
      has_substate σ -∗
      ▷ (£ 1 -∗  has_substate ((err, h, laterO_map k) :: σ) -∗ WP@{rs} β @ s {{ β, Φ β }}) -∗
      WP@{rs} k (_REG err h b) @ s {{ Φ }}.
    Proof.
      iIntros (Hβ) "Hσ Ha".
      unfold _REG. simpl.
      rewrite hom_vis.
      iApply (wp_subreify_ctx_dep _ _ _ _ _ _ _ _ _ _ _ _ [] with "Hσ").
      - simpl.
        rewrite /ccompose /compose /=.
        f_equiv.
        split; simpl; last reflexivity.
        split; simpl; first reflexivity.
        apply cons_equiv; last done.
        apply pair_equiv.
        split; first done.
        trans (laterO_map k : laterO IT -n> laterO IT); last reflexivity.
        intro. simpl. f_equiv. apply ofe_iso_21.
      - apply Hβ.
      - rewrite /weakestpre.wptp big_sepL2_nil.
        iNext. iIntros "H1 H2".
        iSplit; last done.
        iApply ("Ha" with "H1 H2").
    Qed.

    Lemma wp_pop (σ σ': stateF ♯ IT) (err : excO) h k (k' : IT -n> IT) {Hk' : IT_hom k'} β Φ :
      σ = (err,h,k)::σ' →
      k (later_map k' $ Next $ Ret ()) ≡ Next β →
      has_substate σ -∗
      ▷ (£ 1 -∗ has_substate σ' -∗ WP@{rs} β {{ β, Φ β }}) -∗
      WP@{rs} k' (_POP err) {{ Φ }}.
    Proof.
      iIntros (-> Hβ) "Hσ Ha".
      unfold _POP.
      simpl.
      rewrite hom_vis.
      iApply (wp_subreify_ctx_dep with "Hσ").
      - simpl.
        destruct (eq_dec err err); last done.
        reflexivity.
      - exact Hβ. 
      - rewrite /weakestpre.wptp big_sepL2_nil.
        iNext. iIntros "H1 H2".
        iSplit; last done.
        iApply ("Ha" with "H1 H2").
    Qed.
    
    Lemma wp_catch_v σ (v : IT) Φ err h (k : IT -n> IT) {Hk : IT_hom k} `{!AsVal v} β :
      k v ≡ β → 
      has_substate σ -∗
      ▷ (£ 2 -∗ has_substate σ -∗ WP@{rs} β {{ Φ }}) -∗
      WP@{rs} k (CATCH err h v) {{ Φ }}.
    Proof.
      iIntros (Hβ) "Hσ Ha".
      simpl.
      iApply (wp_reg _ _ _ k with "Hσ"); first done.
      iIntros "!> Hcr Hσ".
      simpl.
      rewrite get_val_ITV /=.
      iApply (wp_pop with "Hσ").
      - reflexivity.
      - simpl. unfold later_map. simpl. rewrite get_val_ret. simpl. rewrite Hβ. reflexivity.
      - iNext. iIntros "H1 H2".
        iApply ("Ha" with "[H1 Hcr] H2").
        iSplitL "H1"; done.
    Qed.

    Global Instance throw_hom {err : exc} : IT_hom (THROW err : IT -n> IT).
    Proof.
      simple refine (IT_HOM _ _ _ _ _); intros; simpl.
      - by rewrite hom_tick.
      - rewrite hom_vis. do 3 f_equiv. intro. simpl. done.
      - by rewrite hom_err.
    Qed.
         
    Definition wp_throw (σ pre post : stateF ♯ IT) (err : excO) (h k : laterO IT -n> laterO IT) (k' : IT -n> IT) {Hk : IT_hom k'} (v : IT) `{!AsVal v} β Φ : 
      (Forall (λ '(err',_,_), err <> err') pre) →
      k (h (Next v)) ≡ Next β →
      σ = pre ++ (err,h,k) :: post →
      has_substate σ -∗
      ▷ (£ 1 -∗ has_substate post -∗ WP@{rs} β {{ β, Φ β }}) -∗
      WP@{rs} k' (THROW err v) {{ Φ }}.
    Proof.
      iIntros (Hpre Hβ Hsplit) "Hσ Ha".
      simpl.
      rewrite get_val_ITV.
      rewrite hom_vis.
      iApply (wp_subreify_ctx_dep with "Hσ").
      - simpl.
        change (_cut_when (aux err) σ) with (cut_when (aux err) σ). 
        rewrite (cut_when_first_occ _ σ _ _ _ Hsplit).
        + reflexivity.
        + simpl. destruct (eq_dec err err); done.
        + eapply Forall_impl; first by apply Hpre.
          intros x Hx.
          simpl.
          destruct x as [[err' _] _] . simpl in *.
          destruct (eq_dec err err'); done.
      - exact Hβ.
      - iNext. iIntros "H1 H2".
        rewrite /weakestpre.wptp big_sepL2_nil.
        iSplit; last done.
        iApply ("Ha" with "H1 H2").        
    Qed. 
    
    Lemma wp_catch_throw σ (v : IT) `{!AsVal v} (k k': IT -n> IT) {Hk : IT_hom k} {Hk' : IT_hom k'} Φ err (h : laterO IT -n> laterO IT) β :
      h (Next v) ≡ Next β →
      has_substate σ -∗
      ▷ (£ 1 -∗ has_substate σ -∗ WP@{rs} k' β {{ Φ }}) -∗
      WP@{rs} k' (CATCH err h (k (THROW err v))) {{ Φ }}.
    Proof.
      iIntros (Hβ) "Hσ Ha".
      simpl.
      iApply (wp_reg _ _ _ k' with "Hσ"); first done.
      iIntros "!> Hcr Hσ".
      simpl.
      assert (H : ∀ x y, (get_val x (k y)) = ((get_val x) ∘ k) y).
      { intros. reflexivity. }
      rewrite H.
      iApply (wp_throw _ _ _ _ _ _ ((get_val _) ◎ k) with "Hσ").
      - by apply Forall_nil.
      - trans (laterO_map k' (h (Next v))); first reflexivity.
        rewrite Hβ /= /later_map /=. reflexivity.
      - simpl. reflexivity.
      - iAssumption.
    Qed.

  End weakestpre.
  
End Exc.
