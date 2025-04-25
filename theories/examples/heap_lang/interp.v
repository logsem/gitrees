From gitrees Require Import gitree.
From gitrees.effects Require Import store fork.
From gitrees.lib Require Import pairs sums eq.
From gitrees.examples.heap_lang Require Import lang metatheory notation.
From stdpp Require Import binders stringmap.

Import PrimOps.
Import IF_bool.
Import xchg_wp faa_wp cas_wp.

Lemma ccompose_assoc {A B C D : ofe} (f : C -n> D) (g : B -n> C) (h : A -n> B) :
  f ◎ g ◎ h ≡ f ◎ (g ◎ h).
Proof.
  intros x; simpl.
  reflexivity.
Qed.

Lemma laterO_map_compose' :
  ∀ {A B C : ofe} (f : A -n> B) (g : B -n> C),
  laterO_map (g ◎ f) ≡ laterO_map g ◎ (laterO_map f).
Proof.
  intros ????? ?; simpl.
  rewrite later_map_compose.
  reflexivity.
Qed.

Canonical Structure base_litO := leibnizO base_lit.
Canonical Structure stringO := leibnizO string.

(* move to prelude *)
Section sumO_iso.
  Program Definition sumO_compat_r {A B C : ofe} : A ≃ B → sumO C A ≃ sumO C B
    := λ i, OfeIso
              (λne s, match s with | inl x => inl x | inr x => inr (i x) end)
              (λne s, match s with | inl x => inl x | inr x => inr ((i ^-1) x) end)
              _ _.
  Next Obligation.
    intros ??? i n [|] [|] H; inversion H; subst; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros ??? i n [|] [|] H; inversion H; subst; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros ??? i [x | x]; simpl; first done.
    f_equiv.
    apply (ofe_iso_12 i x).
  Qed.
  Next Obligation.
    intros ??? i [x | x]; simpl; first done.
    f_equiv.
    apply (ofe_iso_21 i x).
  Qed.

  Program Definition sum_iso_cong {A B C D : ofe} :
    A ≃ C → B ≃ D → sumO A B ≃ sumO C D :=
    λ i i', iso_ofe_trans (sumO_compat_l _ _ _ i) (sumO_compat_r i').
End sumO_iso.

(* move to SubOfe *)
Section SubOfeTrans.
  Context {A : ofe} (B : ofe) {C : ofe}.
  Context `{!SubOfe A B} `{!SubOfe B C}.
  Global Program Instance SubOfeTrans : SubOfe A C :=
    Build_SubOfe
      A
      C
      (sumO (subOfe_rest (A := A) (B := B)) (subOfe_rest (A := B) (B := C)))
      (iso_ofe_trans (sumO_assoc
                            A
                            (subOfe_rest (A := A) (B := B))
                            (subOfe_rest (A := B) (B := C)))
             (iso_ofe_trans
                (sum_iso_cong subOfe_in iso_ofe_refl) subOfe_in)).
End SubOfeTrans.

Section SubOfeIso.
  Global Program Instance SubOfeIso (A B : ofe) {C D : ofe} :
    A ≃ C → B ≃ D → SubOfe A B → SubOfe C D :=
    λ i i' H,
      Build_SubOfe C D
        (subOfe_rest (A := A) (B := B))
        (iso_ofe_trans (iso_ofe_sym (sumO_compat_l _ _ _ i))
           (iso_ofe_trans (subOfe_in (A := A) (B := B)) i')).
End SubOfeIso.

Program Definition boolO_decomp_iso : sumO boolO (sumO ZO (sumO locO unitO)) ≃ base_litO
  := OfeIso
       (sumO_rec (λne x, LitBool x)
          (sumO_rec (λne x, LitInt x)
             (sumO_rec (λne x, LitLoc x) (λne _, LitUnit))))
       (λne p, match p with
               | LitBool b => inl b
               | LitInt n => inr (inl n)
               | LitLoc l => inr (inr (inl l))
               | LitUnit => inr (inr (inr ()))
       end)
       _
       _.
Next Obligation.
  intros y; simpl; by destruct y.
Qed.
Next Obligation.
  intros y; simpl; destruct y as [|[|[|]]];
    [reflexivity | reflexivity | reflexivity | by do 3 f_equiv].
Qed.

Program Definition unitO_decomp_iso : sumO unitO (sumO ZO (sumO locO boolO)) ≃ base_litO
  := OfeIso
       (sumO_rec (λne _, LitUnit)
          (sumO_rec (λne x, LitInt x)
             (sumO_rec (λne x, LitLoc x) (λne x, LitBool x))))
       (λne p, match p with
               | LitUnit => inl ()
               | LitInt n => inr (inl n)
               | LitLoc l => inr (inr (inl l))
               | LitBool b => inr (inr (inr b))
       end)
       _
       _.
Next Obligation.
  intros y; simpl; by destruct y.
Qed.
Next Obligation.
  intros y; simpl; destruct y as [|[|[|]]];
    [by f_equiv | reflexivity | reflexivity | reflexivity].
Qed.

Program Definition locO_decomp_iso : sumO locO (sumO ZO (sumO unitO boolO)) ≃ base_litO
  := OfeIso
       (sumO_rec (λne x, LitLoc x)
          (sumO_rec (λne x, LitInt x)
             (sumO_rec (λne _, LitUnit) (λne x, LitBool x))))
       (λne p, match p with
               | LitLoc l => inl l
               | LitInt n => inr (inl n)
               | LitUnit => inr (inr (inl ()))
               | LitBool b => inr (inr (inr b))
       end)
       _
       _.
Next Obligation.
  intros y; simpl; by destruct y.
Qed.
Next Obligation.
  intros y; simpl; destruct y as [|[|[|]]];
    [reflexivity | reflexivity | by do 3 f_equiv | reflexivity].
Qed.

Program Definition ZO_decomp_iso : sumO ZO (sumO locO (sumO unitO boolO)) ≃ base_litO
  := OfeIso
       (sumO_rec (λne x, LitInt x)
          (sumO_rec (λne x, LitLoc x)
             (sumO_rec (λne _, LitUnit) (λne x, LitBool x))))
       (λne p, match p with
               | LitLoc l => inr (inl l)
               | LitInt n => inl n
               | LitUnit => inr (inr (inl ()))
               | LitBool b => inr (inr (inr b))
       end)
       _
       _.
Next Obligation.
  intros y; simpl; by destruct y.
Qed.
Next Obligation.
  intros y; simpl; destruct y as [|[|[|]]];
    [reflexivity | reflexivity | by do 3 f_equiv | reflexivity].
Qed.

Global Program Instance boolO_base_litO : SubOfe boolO base_litO
  := Build_SubOfe
       boolO
       base_litO
       (sumO ZO (sumO locO unitO))
       boolO_decomp_iso.

Global Program Instance unitO_base_litO : SubOfe unitO base_litO
  := Build_SubOfe
       unitO
       base_litO
       (sumO ZO (sumO locO boolO))
       unitO_decomp_iso.

Global Program Instance locO_base_litO : SubOfe locO base_litO
  := Build_SubOfe
       locO
       base_litO
       (sumO ZO (sumO unitO boolO))
       locO_decomp_iso.

Global Program Instance ZO_base_litO : SubOfe ZO base_litO
  := Build_SubOfe
       ZO
       base_litO
       (sumO locO (sumO unitO boolO))
       ZO_decomp_iso.

Section interp.
  Context {sz : nat}.
  Variable (rs : gReifiers NotCtxDep sz).
  Context `{!subReifier reify_store rs
      , !subReifier reify_fork rs}.
  Context {R} `{CR : !Cofe R} `{!Ofe_decide_eq R}.
  Context `{so : !SubOfe base_litO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).

  Canonical Structure varsO : ofe := gmap.gmapO string IT.

  Global Instance : SubOfe boolO R :=
    (SubOfeTrans base_litO).
  Global Instance : SubOfe locO R :=
    (SubOfeTrans base_litO).
  Global Instance : SubOfe unitO R :=
    (SubOfeTrans base_litO).
  Global Instance : SubOfe ZO R :=
    (SubOfeTrans base_litO).

  Program Definition interp_lit (b : base_lit) {A}
    : A -n> IT := λne env, Ret b.

  Global Instance interp_lit_val (b : base_lit) {A : ofe} {env : A}
    : core.AsVal (interp_lit b env).
  Proof. destruct b; apply _. Qed.

  Program Definition interp_pair {A} (a b : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v1, get_val (λne v2, pairITV v2 v1) (a env)) (b env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_proj1 {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, projIT1 (a env).
  Next Obligation. solve_proper. Qed.

  Program Definition interp_proj2 {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, projIT2 (a env).
  Next Obligation. solve_proper. Qed.

  Program Definition interp_inl {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v, injl_ITf v) (a env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_inr {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v, injr_ITf v) (a env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_case {A} (a b c : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v, bimap_IT v (b env) (c env)) (a env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_app {A} (a b : A -n> IT)
    : A -n> IT :=
    λne env, APP' (a env) (b env).
  Next Obligation. solve_proper. Qed.

  Opaque laterO_map.
  Program Definition interp_rec_pre (f x : binder) (body : varsO -n> IT)
    : laterO (varsO -n> IT) -n> varsO -n> IT :=
    λne self env, Fun $ laterO_map (λne (self : varsO -n> IT) (a : IT),
                      body (binder_insert x a (binder_insert f (self env) env))) self.
  Next Obligation.
    intros f x body l env self n a b H.
    f_equiv.
    unfold binder_insert.
    destruct x, f; [done | done | by rewrite H | by f_equiv].
  Qed.
  Next Obligation.
    intros f x body self env n a b H l; simpl.
    f_equiv.
    unfold binder_insert.
    destruct x, f; [done | by f_equiv | done | by do 2 f_equiv].
  Qed.
  Next Obligation.
    intros f x body self n a b H.
    do 3 f_equiv.
    intros self' a'; simpl.
    f_equiv.
    unfold binder_insert.
    destruct x, f; [done | by rewrite H | by rewrite H | by rewrite H].
  Qed.
  Next Obligation.
    intros f x body n a b H env; simpl.
    by do 2 f_equiv.
  Qed.

  Definition interp_rec f x body : varsO -n> IT := mmuu (interp_rec_pre f x body).
  Program Definition ir_unf f x (body : varsO -n> IT) env : IT -n> IT :=
    λne a, body (binder_insert x a (binder_insert f ((interp_rec f x body) env) env)).
  Next Obligation.
    intros f x body env n a b H.
    f_equiv.
    unfold binder_insert.
    destruct x, f; [done | by f_equiv | by rewrite H | by rewrite H].
  Qed.

  Lemma interp_rec_unfold f x (body : varsO -n> IT) env :
    interp_rec f x body env ≡ Fun $ Next $ ir_unf f x body env.
  Proof.
    trans (interp_rec_pre f x body (Next (interp_rec f x body)) env).
    { f_equiv. rewrite /interp_rec. apply mmuu_unfold. }
    simpl. rewrite laterO_map_Next. repeat f_equiv.
    simpl. unfold ir_unf. intro. simpl. reflexivity.
  Qed.
  Transparent laterO_map.

  Program Definition interp_var (x : string) : varsO -n> IT :=
    λne env, from_option idfun (Err RuntimeErr) (env !! x).
  Solve All Obligations with solve_proper.

  Program Definition interp_if {A} (a b c : A -n> IT)
    : A -n> IT :=
    λne env, IF (a env) (b env) (c env).
  Next Obligation. solve_proper. Qed.

  Program Definition interp_fork {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, FORK (a env).
  Next Obligation. solve_proper. Qed.

  Program Definition interp_store {A} (a b : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v, get_ret (λne l, WRITE l v) (a env)) (b env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_load {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, get_ret (λne l, READ l) (a env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_free {A} (a : A -n> IT)
    : A -n> IT :=
    λne env, get_ret (λne l, DEALLOC l) (a env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_xchg {A} (a b : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v, get_ret (λne l, XCHG l v) (a env)) (b env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_cas {A} (a b c : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v1, get_val (λne v2, get_ret (λne l, CAS l v1 v2) (a env)) (b env)) (c env).
  Solve All Obligations with solve_proper_please.

  Program Definition incr_ne : ZO -n> ZO -n> ZO := λne x y : ZO, (x + y)%Z.
  Program Definition interp_faa {A} (a b : A -n> IT)
    : A -n> IT :=
    λne env, get_val (λne v, get_ret (λne l, FAA incr_ne l v) (a env)) (b env).
  Solve All Obligations with solve_proper_please.

  Definition get_natZ : Z → option nat :=
    λ z : Z, match z with
             | Z.pos p => Some (Pos.to_nat p)
             | _ => None
             end.

  Global Instance to_nat_ne : NonExpansive Pos.to_nat.
  Proof.
    intros n a b H.
    rewrite /Pos.to_nat.
    solve_proper.
  Qed.
  Global Instance get_natZ_ne : NonExpansive get_natZ.
  Proof.
    solve_proper.
  Qed.

  Program Definition interp_alloc_n {A} (a b : A -n> IT)
    : A -n> IT :=
    λne env, get_val
               (λne v, get_ret
                         (λne p, from_option
                                   (λne x, ALLOC_N x v Ret)
                                   (Err RuntimeErr) (get_natZ p)) (a env)) (b env).
  Solve All Obligations with solve_proper_please.

  Program Definition interp_unop {A} (op : un_op) (a : A -n> IT)
    : A -n> IT := λne env, UNOP (λne x : base_litO, un_op_eval_lit op x) (a env).
  Solve All Obligations with solve_proper.

  Program Definition interp_binop {A} (op : bin_op) (a b : A -n> IT)
    : A -n> IT := λne env, BINOP (λne x y : base_litO, bin_op_eval_lit op x y) (a env) (b env).
  Solve All Obligations with solve_proper_please.

  Fixpoint interp_expr (e : expr) : varsO -n> IT :=
    match e with
    | Val v => interp_val v
    | Var x => interp_var x
    | Rec f x e => interp_rec f x (interp_expr e)
    | App e1 e2 => interp_app (interp_expr e1) (interp_expr e2)
    | UnOp op e => interp_unop op (interp_expr e)
    | BinOp op e1 e2 => interp_binop op (interp_expr e1) (interp_expr e2)
    | If e0 e1 e2 => interp_if (interp_expr e0) (interp_expr e1) (interp_expr e2)
    | Pair e1 e2 => interp_pair (interp_expr e1) (interp_expr e2)
    | Fst e => interp_proj1 (interp_expr e)
    | Snd e => interp_proj2 (interp_expr e)
    | InjL e => interp_inl (interp_expr e)
    | InjR e => interp_inr (interp_expr e)
    | Case e0 e1 e2 => interp_case (interp_expr e0) (interp_expr e1) (interp_expr e2)
    | AllocN e1 e2 => interp_alloc_n (interp_expr e1) (interp_expr e2)
    | Free e => interp_free (interp_expr e)
    | Load e => interp_load (interp_expr e)
    | Store e1 e2 => interp_store (interp_expr e1) (interp_expr e2)
    | CmpXchg e0 e1 e2 => interp_cas (interp_expr e0) (interp_expr e1) (interp_expr e2)
    | Xchg e0 e1 => interp_xchg (interp_expr e0) (interp_expr e1)
    | heap_lang.FAA e1 e2 => interp_faa (interp_expr e1) (interp_expr e2)
    | Fork e => interp_fork (interp_expr e)
    end
  with interp_val (v : val) : varsO -n> IT :=
         match v with
         | LitV l => interp_lit l
         | RecV f x e => interp_rec f x (interp_expr e)
         | PairV v1 v2 => interp_pair (interp_val v1) (interp_val v2)
         | InjLV v => interp_inl (interp_val v)
         | InjRV v => interp_inr (interp_val v)
         end.

  Global Instance interp_val_val (v : val) (env : varsO)
    : core.AsVal (interp_val v env).
  Proof.
    induction v; [apply _ | | | | ]; simpl.
    - rewrite interp_rec_unfold.
      apply _.
    - rewrite get_val_ITV /= get_val_ITV /=.
      apply _.
    - rewrite get_val_ITV /=.
      apply _.
    - rewrite get_val_ITV /=.
      apply _.
  Qed.

  Program Definition interp_applk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_app (λne env, K env t) q env.
  Solve All Obligations with solve_proper.

  Program Definition interp_apprk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_app q (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_ifk {A}
    (q : A -n> IT)
    (p : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_if (λne env, K env t) q p env.
  Solve All Obligations with solve_proper.

  Program Definition interp_unopk {A} (op : un_op)
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_unop op (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_binoprk {A} (op : bin_op)
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_binop op q (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_binoplk {A} (op : bin_op)
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_binop op (λne env, K env t) q env.
  Solve All Obligations with solve_proper.

  Program Definition interp_proj1k {A}
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_proj1 (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_proj2k {A}
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_proj2 (λne env, K env t) env.
  Solve All Obligations with solve_proper.

  Program Definition interp_inlk {A}
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_inl (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_inrk {A}
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_inr (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_pairlk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_pair (λne env, K env t) q env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_pairrk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_pair q (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_casek {A}
    (q p : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_case (λne env, K env t) q p env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_freek {A}
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_free (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_loadk {A}
    (K : A -n> (IT -n> IT)) : A -n> (IT -n> IT) :=
    λne env t, interp_load (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_allocnlk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_alloc_n (λne env, K env t) q env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_allocnrk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_alloc_n q (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_storelk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_store (λne env, K env t) q env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_storerk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_store q (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_xchglk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_xchg (λne env, K env t) q env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_xchgrk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_xchg q (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_faalk {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_faa (λne env, K env t) q env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_faark {A}
    (q : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_faa q (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_cas1 {A}
    (q p : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_cas (λne env, K env t) q p env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_cas2 {A}
    (q p : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_cas q p (λne env, K env t) env.
  Solve All Obligations with solve_proper_please.

  Program Definition interp_cas3 {A}
    (q p : A -n> IT)
    (K : A -n> (IT -n> IT))
    : A -n> (IT -n> IT) :=
    λne env t, interp_cas q (λne env, K env t) p env.
  Solve All Obligations with solve_proper_please.

  Definition interp_ectx_item (K : ectx_item)
    : (varsO -n> (IT -n> IT)) → varsO -n> (IT -n> IT) :=
    match K with
    | AppLCtx v2 =>
        interp_applk (interp_val v2)
    | AppRCtx e1 =>
        interp_apprk (interp_expr e1)
    | UnOpCtx op =>
        interp_unopk op
    | BinOpLCtx op v2 =>
        interp_binoplk op (interp_val v2)
    | BinOpRCtx op e1 =>
        interp_binoprk op (interp_expr e1)
    | IfCtx e1 e2 =>
        interp_ifk (interp_expr e1) (interp_expr e2)
    | PairLCtx v2 =>
        interp_pairlk (interp_val v2)
    | PairRCtx e1 =>
        interp_pairrk (interp_expr e1)
    | FstCtx =>
        interp_proj1k
    | SndCtx =>
        interp_proj2k
    | InjLCtx =>
        interp_inlk
    | InjRCtx =>
        interp_inrk
    | CaseCtx e1 e2 =>
        interp_casek (interp_expr e1) (interp_expr e2)
    | AllocNLCtx v2 =>
        interp_allocnlk (interp_val v2)
    | AllocNRCtx e1 =>
        interp_allocnrk (interp_expr e1)
    | FreeCtx =>
        interp_freek
    | LoadCtx =>
        interp_loadk
    | StoreLCtx v2 =>
        interp_storelk (interp_val v2)
    | StoreRCtx e1 =>
        interp_storerk (interp_expr e1)
    | XchgLCtx v2 =>
        interp_xchglk (interp_val v2)
    | XchgRCtx e1 =>
        interp_xchgrk (interp_expr e1)
    | CmpXchgLCtx v1 v2 =>
        interp_cas1 (interp_val v1) (interp_val v2)
    | CmpXchgMCtx e0 v2 =>
        interp_cas3 (interp_expr e0) (interp_val v2)
    | CmpXchgRCtx e0 e1 =>
        interp_cas2 (interp_expr e0) (interp_expr e1)
    | FaaLCtx v2 =>
        interp_faalk (interp_val v2)
    | FaaRCtx e1 =>
        interp_faark (interp_expr e1)
    end.

  #[local] Instance interp_applk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_applk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite hom_tick -APP'_Tick_l //=.
    - rewrite hom_vis.
      rewrite APP'_Vis_l.
      f_equiv.
      rewrite -ccompose_assoc.
      rewrite -laterO_map_compose'.
      do 2 f_equiv.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      rewrite APP_APP'_ITV.
      reflexivity.
    - rewrite hom_err APP'_Err_l //=.
  Qed.

  Opaque laterO_map.
  #[local] Instance interp_apprk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_apprk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite hom_tick -APP'_Tick_r //=.
    - rewrite !hom_vis. f_equiv. intro x. simpl.
      rewrite laterO_map_compose.
      reflexivity.
    - by rewrite !hom_err.
  Qed.
  Transparent laterO_map.

  #[local] Instance interp_ifk_hom {A}
    (K : A -n> IT -n> IT) (e1 e2 : A -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_ifk e1 e2 K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -IF_Tick hom_tick //=.
    - rewrite hom_vis IF_Vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl. rewrite -later_map_compose /=.
      f_equiv.
    - rewrite hom_err IF_Err //=.
  Qed.

  #[local] Instance interp_unopk_hom {A}
    (K : A -n> IT -n> IT) op env :
    IT_hom (K env) →
    IT_hom (interp_unopk op K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite /UNOP /UNOP_ne hom_tick get_val_tick //=.
    - rewrite /UNOP /UNOP_ne hom_vis get_val_vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl. rewrite -later_map_compose /=.
      f_equiv.
    - rewrite /UNOP /UNOP_ne hom_err get_val_err //=.
  Qed.

  #[local] Instance interp_binoprk_hom {A}
    (K : A -n> IT -n> IT) op (e : A -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_binoprk op e K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite /BINOP /BINOP_ne hom_tick get_val_tick //=.
    - rewrite /BINOP /BINOP_ne hom_vis get_val_vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl. rewrite -later_map_compose /=.
      f_equiv.
    - rewrite /BINOP /BINOP_ne hom_err get_val_err //=.
  Qed.

  Opaque laterO_map.
  #[local] Instance interp_binoplk_hom {A}
    (K : A -n> IT -n> IT) op (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_binoplk op e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite /BINOP /BINOP_ne /= get_val_ITV /= hom_tick get_val_tick /=.
      f_equiv.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite /BINOP /BINOP_ne /= get_val_ITV /= hom_vis get_val_vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite /BINOP /BINOP_ne /= get_val_ITV /= hom_err get_val_err //=.
  Qed.
  Transparent laterO_map.

  #[local] Instance interp_proj1k_hom {A}
    (K : A -n> IT -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_proj1k K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite hom_tick !APP'_Fun_r APP_Tick //=.
    - rewrite hom_vis !APP'_Vis_l.
      f_equiv.
      rewrite -ccompose_assoc.
      rewrite -laterO_map_compose'.
      do 2 f_equiv.
      intros ?; simpl.
      rewrite get_val_fun /=.
      rewrite APP'_Fun_r.
      reflexivity.
    - rewrite hom_err APP'_Fun_r APP_Err //=.
  Qed.

  #[local] Instance interp_proj2k_hom {A}
    (K : A -n> IT -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_proj2k K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite hom_tick !APP'_Fun_r APP_Tick //=.
    - rewrite hom_vis !APP'_Vis_l.
      f_equiv.
      rewrite -ccompose_assoc.
      rewrite -laterO_map_compose'.
      do 2 f_equiv.
      intros ?; simpl.
      rewrite get_val_fun /=.
      rewrite APP'_Fun_r.
      reflexivity.
    - rewrite hom_err APP'_Fun_r APP_Err //=.
  Qed.

  Opaque laterO_map.
  #[local] Instance interp_pairlk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_pairlk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= hom_tick get_val_ITV /= get_val_tick //=.
    - rewrite get_val_ITV /= hom_vis get_val_vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= hom_err get_val_err //=.
  Qed.
  Transparent laterO_map.

  #[local] Instance interp_freek_hom {A}
    (K : A -n> IT -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_freek K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick -hom_tick //=.
    - rewrite hom_vis get_ret_vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl. rewrite -later_map_compose /=.
      f_equiv.
    - rewrite hom_err get_ret_err //=.
  Qed.

  #[local] Instance interp_loadk_hom {A}
    (K : A -n> IT -n> IT) env :
    IT_hom (K env) →
    IT_hom (interp_loadk K env).
  Proof.
    intros H.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite -hom_tick -hom_tick //=.
    - rewrite hom_vis get_ret_vis /=.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl. rewrite -later_map_compose /=.
      f_equiv.
    - rewrite hom_err get_ret_err //=.
  Qed.

  Opaque laterO_map.
  #[local] Instance interp_allocnlk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_allocnlk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_tick get_ret_tick //=.
    - rewrite get_val_ITV /=.
      rewrite hom_vis get_ret_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /=.
      rewrite hom_err get_ret_err //=.
  Qed.
  Transparent laterO_map.

  Opaque laterO_map.
  #[local] Instance interp_storelk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_storelk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_tick get_ret_tick //=.
    - rewrite get_val_ITV /=.
      rewrite hom_vis get_ret_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /=.
      rewrite hom_err get_ret_err //=.
  Qed.
  Transparent laterO_map.

  Opaque laterO_map.
  #[local] Instance interp_xchglk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_xchglk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_tick get_ret_tick //=.
    - rewrite get_val_ITV /=.
      rewrite hom_vis get_ret_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /=.
      rewrite hom_err get_ret_err //=.
  Qed.
  Transparent laterO_map.

  Opaque laterO_map.
  #[local] Instance interp_faalk_hom {A}
    (K : A -n> IT -n> IT) (e : A -n> IT) env `{!core.AsVal (e env)} :
    IT_hom (K env) →
    IT_hom (interp_faalk e K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_tick get_ret_tick //=.
    - rewrite get_val_ITV /=.
      rewrite hom_vis get_ret_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /=.
      rewrite hom_err get_ret_err //=.
  Qed.
  Transparent laterO_map.

  Opaque laterO_map.
  #[local] Instance interp_cas1_hom {A}
    (K : A -n> IT -n> IT) (e1 e2 : A -n> IT) env
    `{!core.AsVal (e1 env)} `{!core.AsVal (e2 env)}:
    IT_hom (K env) →
    IT_hom (interp_cas1 e1 e2 K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_tick get_ret_tick //=.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_vis get_ret_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv. simpl.
      intros ?; simpl.
      rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_err get_ret_err //=.
  Qed.
  Transparent laterO_map.

  Opaque laterO_map.
  #[local] Instance interp_cas2_hom {A}
    (K : A -n> IT -n> IT) (e1 e2 : A -n> IT) env `{!core.AsVal (e1 env)} :
    IT_hom (K env) →
    IT_hom (interp_cas2 e1 e2 K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite hom_tick get_val_tick //=.
    - rewrite hom_vis get_val_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv.
      intros ?; simpl.
      reflexivity.
    - rewrite hom_err get_val_err //=.
  Qed.
  Transparent laterO_map.

  Opaque laterO_map.
  #[local] Instance interp_cas3_hom {A}
    (K : A -n> IT -n> IT) (e1 e2 : A -n> IT) env `{!core.AsVal (e2 env)} :
    IT_hom (K env) →
    IT_hom (interp_cas3 e1 e2 K env).
  Proof.
    intros G.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite hom_tick get_val_tick //=.
    - rewrite get_val_ITV /=.
      rewrite hom_vis get_val_vis.
      f_equiv.
      rewrite -ccompose_assoc.
      intros ?; simpl.
      rewrite -laterO_map_compose /=.
      do 2 f_equiv.
      intros ?; simpl.
      rewrite get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /=.
      rewrite hom_err get_val_err //=.
  Qed.
  Transparent laterO_map.

  #[local] Instance interp_ectx_item_hom (K : varsO -n> IT -n> IT) (k : ectx_item)
    (env : varsO) `{!IT_hom (K env)}
    : IT_hom (interp_ectx_item k K env).
  Proof.
    destruct k; simpl; apply _.
  Qed.

  Program Definition idctx {A : ofe} : A -n> IT -n> IT := λne env, idfun.

  Lemma interp_ectx_item_fill (k : ectx_item)
    (env : varsO) e
    : (interp_expr (fill_item k e) env)
        ≡ (interp_ectx_item k idctx env) (interp_expr e env).
  Proof.
    destruct k; simpl; try reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
    - rewrite get_val_ITV /= get_val_ITV /=.
      reflexivity.
  Qed.

  Program Definition interp_ectx (K : ectx heap_ectx_lang) : varsO -n> (IT -n> IT) :=
    λne env, foldl (λ f k, f ◎ interp_ectx_item k idctx env) idfun (rev K).
  Next Obligation.
    intros K n a b H.
    induction K as [| ? ? IH].
    - done.
    - simpl.
      rewrite !foldl_snoc.
      f_equiv.
      + apply IH.
      + by f_equiv.
  Qed.

  Lemma interp_ectx_fill (k : ectx heap_ectx_lang)
    (env : varsO) e
    : (interp_expr (fill k e) env)
        ≡ (interp_ectx k env) (interp_expr e env).
  Proof.
    revert e.
    induction k as [| ? ? IH]; simpl; intros e.
    - reflexivity.
    - rewrite IH.
      rewrite interp_ectx_item_fill.
      rewrite foldl_snoc /=.
      reflexivity.
  Qed.

  Lemma interp_ectx_hom (K : ectx heap_ectx_lang)
    : ∀ ρ : varsO, IT_hom (interp_ectx K ρ).
  Proof.
    induction K as [| ? ? IH]; first apply _.
    intros; simpl.
    apply IT_hom_compose; last apply _.
    rewrite foldl_snoc.
    apply IT_hom_compose; last apply _.
    apply IH.
  Qed.

End interp.

Arguments interp_expr {_ _ _ _ _ _ _ _}.
Arguments interp_val {_ _ _ _ _ _ _ _}.

(* Lemma sfd : Ofe_decide_eq base_litO. *)
(* Proof. *)
(*   unshelve econstructor. *)
(*   - unshelve econstructor. *)
(*     + intros. *)
(*       unshelve econstructor. *)
(*       * intros. *)
(*         apply (bool_decide (X = X0)). *)
(*       * intros ????. *)
(*         simpl in H. *)
(*         rewrite H. *)
(*         reflexivity. *)
(*     + intros ????. *)
(*       simpl in H. *)
(*       rewrite H. *)
(*       reflexivity. *)
(*   - intros ???. *)
(*     simpl in H. *)

(* Section program_logic. *)
(*   Context {sz : nat}. *)
(*   Variable (rs : gReifiers NotCtxDep sz). *)
(*   Context {R} `{CR : !Cofe R} `{SubOfe boolO R}. *)
(*   Notation F := (gReifiers_ops rs). *)
(*   Notation IT := (IT F R). *)
(*   Notation ITV := (ITV F R). *)
(*   Context `{!gitreeGS_gen rs R Σ}. *)

(*   Class ofe_decide_eq T `{!SubOfe T R} := *)
(*     MkOfeDecide { *)
(*         ofe_dec' : IT -n> IT -n> IT; *)
(*         ofe_dec_reflect' : ∀ a b : T, *)
(*           ofe_dec' (Ret a) (Ret b) ≡ Ret true → (Ret a : IT) ≡ (Ret b : IT); *)
(*         (* ofe_dec_hom1 e a : ofe_dec (Tick e) a ≡ Tick (ofe_dec e a); *) *)
(*         (* ofe_dec_hom2 (v : ITV) a : ofe_dec (IT_of_V v) (Tick a) ≡ Tick (ofe_dec (IT_of_V v) a); *) *)
(*       }. *)

(*   Global Program Instance ofe_decide_eq_base_litO `{!SubOfe base_litO R} : *)
(*     ofe_decide_eq base_litO *)
(*     := MkOfeDecide base_litO _ (get_ret2 (λne x y, Ret (bool_decide (x = y)))) _. *)
(*   Next Obligation. *)
(*     intros ? x y K. *)
(*     rewrite /get_ret2 /= in K. *)
(*     rewrite get_ret_ret /= get_ret_ret /= in K. *)
(*     apply bi.siProp.internal_eq_soundness. *)
(*     iDestruct (Ret_inj (E := F) (A := boolO) (B := R) true false) as "J". *)
(*     destruct (bool_decide (x = y)) as [G | G] eqn:J. *)
(*     - rewrite bool_decide_eq_true in J. *)
(*       by rewrite J. *)
(*     - iEval (rewrite K) in "J". *)
(*       iExFalso. *)
(*       iDestruct "J" as "[_ J]". *)
(*       iDestruct ("J" with "[]") as "J'"; first done. *)
(*       iDestruct (discrete_eq with "J'") as "%P". *)
(*       inversion P. *)
(*   Qed. *)

(*   Lemma sdfsdf (w1 w2 : val) (env : varsO rs) *)
(*     `{!SubOfe base_litO R} *)
(*     `{!subReifier reify_store rs *)
(*       , !subReifier reify_fork_sig rs} *)
(*     `{!Ofe_decide_eq R} *)
(*     : vals_compare_safe w1 w2 → w1 = w2 → *)
(*       (ofe_dec' (interp_val w1 env) (interp_val w2 env) ≡ Ret true). *)
(*   Proof. *)
(*     intros J ->. *)
(*     unfold ofe_dec'. *)
(*     simpl. *)
(*     destruct J. *)
(*     - destruct w2; simpl in H0; [| inversion H0 | inversion H0 | |]. *)
(*       + rewrite get_ret_ret /= get_ret_ret /=. *)

(*         admit. *)
(*       + destruct w2; simpl in H0; [| inversion H0 | inversion H0 | |]. *)
(*         * simpl. *)
(*           match goal with *)
(*           | |- context G [ofe_mor_car _ _ (get_ret ?a) ?b] => *)
(*               set (F := b) *)
(*           end. *)
(*           assert (F ≡ injl_ITf (Ret l)) as ->. *)
(*           { unfold injl_ITf. *)
(*             simpl. *)
(*             subst F. *)
(*             rewrite get_val_ret /=. *)
(*             reflexivity. *)
(*           } *)
(*           simpl. *)

(*           set (F := (get_val (λne v : IT, λit l0 : IT, λit _ : IT, l0 ⊙ v) (Ret l))). *)
(*           admit. *)
(*         * admit. *)
(*         * admit. *)
(*       + admit. *)
(*     - destruct w2; simpl in H; [| inversion H | inversion H | |]. *)
(*       + rewrite get_ret_ret /= get_ret_ret /=. *)
(*         admit. *)
(*       + destruct w2; simpl in H; [| inversion H | inversion H | |]. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*       + admit. *)
(*   Admitted. *)

(* End program_logic. *)

Section program_logic.
  Context {sz : nat}.
  Variable (rs : gReifiers NotCtxDep sz).
  Context `{!subReifier reify_store rs
      , !subReifier reify_fork_sig rs}.
  Context {R} `{CR : !Cofe R} `{!Ofe_decide_eq R}.
  Context `{so : !SubOfe base_litO R}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F R).
  Notation ITV := (ITV F R).
  Context `{!gitreeGS_gen rs R Σ, !heapG rs R Σ}.

  Lemma interp_wp_fork σ (n : IT) Φ (e : expr) (env : varsO rs) :
    has_substate σ
    -∗ ▷ (£ 1 -∗ has_substate σ
          -∗ WP@{rs} (Ret ()) {{ Φ }}
           ∗ ▷ WP@{rs} (interp_expr e env) {{ fork_post }})
    -∗ WP@{rs} (interp_expr (Fork e) env) {{ Φ }}.
  Proof.
    iIntros "H G".
    iEval (unfold interp_expr at 1).
    match goal with
    | |- context G [ interp_fork _ (_ ?a)] =>
        fold (interp_expr a)
    end.
    iApply (wp_fork rs _ _ idfun with "H G").
  Qed.

  Lemma wp_cas_fail_hom (l : store.locO) α (w1 w2 : val) Φ (env : varsO rs) :
    heap_ctx rs
    -∗ ▷ pointsto l (interp_val α env)
    -∗ ▷ (safe_compare (interp_val w2 env) (interp_val α env) ≡ Ret false)
    -∗ ▷ ▷ (pointsto l (interp_val α env)
            -∗ WP@{rs} ((pairIT (interp_val α env) (Ret false))) {{ Φ }})
    -∗ WP@{rs} (interp_expr (CmpXchg #l w1 w2) env) {{ Φ }}.
  Proof.
    iIntros "#Hcxt H HEQ G".
    unfold interp_expr at 1.
    match goal with
    | |- context G [ interp_cas _ _ (_ ?a) (_ ?b)] =>
        fold (interp_expr a); fold (interp_expr b)
    end.
    iEval (rewrite /interp_cas /= get_val_ITV /= get_val_ITV /= get_ret_ret /=).
    iApply (wp_cas_fail_hom rs _ _ _ _ _ _ idfun with "Hcxt H [HEQ] G").
    iApply "HEQ".
  Qed.

  Lemma wp_cas_succ_hom (l : store.locO) α (w1 w2 : val) Φ (env : varsO rs) :
    heap_ctx rs
    -∗ ▷ pointsto l (interp_val α env)
    -∗ ▷ (safe_compare (interp_val w2 env) (interp_val α env) ≡ Ret true)
    -∗ ▷ ▷ (pointsto l (interp_val w1 env)
            -∗ WP@{rs} ((pairIT (interp_val α env) (Ret true))) {{ Φ }})
    -∗ WP@{rs} (interp_expr (CmpXchg #l w1 w2) env) {{ Φ }}.
  Proof.
    iIntros "#Hcxt H HEQ G".
    unfold interp_expr at 1.
    match goal with
    | |- context G [ interp_cas _ _ (_ ?a) (_ ?b)] =>
        fold (interp_expr a); fold (interp_expr b)
    end.
    iEval (rewrite /interp_cas /= get_val_ITV /= get_val_ITV /= get_ret_ret /=).
    iApply (wp_cas_succ_hom rs _ _ _ _ _ _ idfun with "Hcxt H [HEQ] G").
    iApply "HEQ".
  Qed.

  Lemma sdfsdf (w1 w2 : val) (env : varsO rs)
    : vals_compare_safe w1 w2 → w1 = w2 →
      (safe_compare (interp_val w1 env) (interp_val w2 env) ≡ Ret true).
  Proof.
    intros H ->.
    rewrite /safe_compare /safe_compare_def /=.
    rewrite get_val_ITV /= get_val_ITV /=.
    destruct H.
    - destruct w2; simpl in H; [| inversion H | inversion H | |].
      + rewrite get_ret_ret /= get_ret_ret /=.

        admit.
      + destruct w2; simpl in H; [| inversion H | inversion H | |].
        * simpl.

          admit.
        * admit.
        * admit.
      + admit.
    - destruct w2; simpl in H; [| inversion H | inversion H | |].
      + rewrite get_ret_ret /= get_ret_ret /=.
        admit.
      + destruct w2; simpl in H; [| inversion H | inversion H | |].
        * admit.
        * admit.
        * admit.
      + admit.
  Admitted.

End program_logic.
