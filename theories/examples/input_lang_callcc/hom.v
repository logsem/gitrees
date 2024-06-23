(** Particular homomorphisms for the call/cc lang *)
From gitrees Require Import gitree lang_generic.
From gitrees Require Export hom.
From gitrees.examples.input_lang_callcc Require Import lang interp.
Require Import Binding.Lib Binding.Set Binding.Env.

Open Scope stdpp_scope.

Section hom.
  Context {sz : nat}.
  Context {rs : gReifiers CtxDep sz}.
  Context {A : ofe}.
  Context {CA : Cofe A}.
  Context `{SubOfe natO A}.
  Context `{!subReifier reify_cont rs}.
  Context `{!subReifier (sReifier_NotCtxDep_CtxDep reify_io) rs}.
  Notation F := (gReifiers_ops rs).
  Notation IT := (IT F natO).
  Notation ITV := (ITV F natO).

  (** Specific packaged homomorphisms *)

  Program Definition NatOpRSCtx_HOM {S : Set} (op : nat_op)
    (α : @interp_scope F A _ S -n> IT) (env : @interp_scope F A _ S)
    : HOM := exist _ (interp_natoprk rs op α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition NatOpLSCtx_HOM {S : Set} (op : nat_op)
    (α : IT) (env : @interp_scope F A _ S)
    (Hv : AsVal α)
    : HOM := exist _ (interp_natoplk rs op (λne env, idfun) (constO α) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition ThrowLSCtx_HOM {S : Set}
    (α : @interp_scope F A _ S -n> IT)
    (env : @interp_scope F A _ S)
    : HOM := exist _ ((interp_throwlk rs (λne env, idfun) α env)) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition ThrowRSCtx_HOM {S : Set}
    (β : IT) (env : @interp_scope F A _ S)
    (Hv : AsVal β)
    : HOM := exist _ (interp_throwrk rs (constO β) (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    simple refine (IT_HOM _ _ _ _ _); intros; simpl.
    - solve_proper_please.
    - destruct Hv as [? <-].
      rewrite ->2 get_val_ITV.
      simpl. by rewrite get_fun_tick.
    - destruct Hv as [x Hv].
      rewrite <- Hv.
      rewrite -> get_val_ITV.
      simpl.
      rewrite get_fun_vis.
      repeat f_equiv.
      intro; simpl.
      rewrite <- Hv.
      by rewrite -> get_val_ITV.
    - destruct Hv as [? <-].
      rewrite get_val_ITV.
      simpl.
      by rewrite get_fun_err.
  Qed.

  Program Definition OutputSCtx_HOM {S : Set}
    (env : @interp_scope F A _ S) : HOM (A:=natO)
    := exist _ ((interp_outputk rs (λne env, idfun) env)) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition AppRSCtx_HOM {S : Set}
    (α : @interp_scope F A _ S -n> IT)
    (env : @interp_scope F A _ S)
    : HOM := exist _ (interp_apprk rs α (λne env, idfun) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

  Program Definition AppLSCtx_HOM {S : Set}
    (β : IT) (env : @interp_scope F A _ S)
    (Hv : AsVal β)
    : HOM := exist _ (interp_applk rs (λne env, idfun) (constO β) env) _.
  Next Obligation.
    intros; simpl.
    apply _.
  Qed.

End hom.
