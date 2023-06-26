From gitrees Require Import prelude.
From gitrees Require Import gitree.
From Equations Require Import Equations.
Require Import List.
Import ListNotations.

(** XXX: We /NEED/ this line for [Equations Derive] to work,
 this flag is globally unset by std++, but Equations need obligations to be transparent. *)
Set Transparent Obligations.

Derive NoConfusion NoConfusionHom for list.

Definition scope := (list unit).

(** Variables in a context *)
Inductive var : scope → Type :=
| Vz : forall {S : scope} {s}, var (s::S)
| Vs : forall {S : scope} {s}, var S -> var (s::S)
.
Derive Signature NoConfusion for var.

Inductive tyctx (ty : Type) : scope → Type :=
| empC : tyctx ty []
| consC : forall{Γ}, ty → tyctx ty Γ → tyctx ty (()::Γ)
.
Arguments empC {_}.
Arguments consC {_ _} _ _.

Equations list_of_tyctx {S ty} (Γ : tyctx ty S) : list ty :=
  list_of_tyctx empC := [];
  list_of_tyctx (consC τ Γ') := τ::list_of_tyctx Γ'.

Equations tyctx_app {S1 S2 ty} (c1 : tyctx ty S1) (c2 : tyctx ty S2) : tyctx ty (S1++S2) :=
  tyctx_app empC         c2 := c2;
  tyctx_app (consC τ c1) c2 := consC τ (tyctx_app c1 c2).

Inductive typed_var {ty : Type}: forall {S}, tyctx ty S → var S → ty → Prop :=
| typed_var_Z S (τ : ty) (Γ : tyctx ty S) :
  typed_var (consC τ Γ) Vz τ
| typed_var_S S (τ τ' : ty) (Γ : tyctx ty S) v :
  typed_var Γ v τ →
  typed_var (consC τ' Γ) (Vs v) τ
.

Section interp.
  Context {E: opsInterp}.
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Fixpoint interp_scope (S : scope) : ofe :=
    match S with
    | [] => unitO
    | τ::Sc => prodO IT (interp_scope Sc)
    end.

  Instance interp_scope_cofe S : Cofe (interp_scope S).
  Proof. induction S; simpl; apply _. Qed.

  Instance interp_scope_inhab S : Inhabited (interp_scope S).
  Proof. induction S; simpl; apply _. Defined.

  Equations interp_var {S : scope} (v : var S) : interp_scope S -n> IT :=
    interp_var (S:=(_::_))     Vz := fstO;
    interp_var (S:=(_::Sc)) (Vs v) := interp_var v ◎ sndO.

  Instance interp_var_ne S (v : var S) : NonExpansive (@interp_var S v).
  Proof.
    intros n D1 D2 HD12. induction v; simp interp_var.
    - by f_equiv.
    - eapply IHv. by f_equiv.
  Qed.

  Global Instance interp_var_proper S (v : var S) : Proper ((≡) ==> (≡)) (interp_var v).
  Proof. apply ne_proper. apply _. Qed.

  (** scope substituions *)
  Inductive ssubst : scope → Type :=
  | emp_ssubst : ssubst []
  | cons_ssubst {S} : ITV → ssubst S → ssubst (()::S)
  .

  Equations interp_ssubst {S} (ss : ssubst S) : interp_scope S :=
    interp_ssubst emp_ssubst := ();
    interp_ssubst (cons_ssubst αv ss) := (IT_of_V αv, interp_ssubst ss).

  Equations list_of_ssubst {S} (ss : ssubst S) : list ITV :=
    list_of_ssubst emp_ssubst := [];
    list_of_ssubst (cons_ssubst αv ss) := αv::(list_of_ssubst ss).

End interp.
