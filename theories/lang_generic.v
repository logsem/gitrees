(* From gitrees Require Import prelude. *)
(* From Equations Require Import Equations. *)
(* Require Import List. *)
(* Import ListNotations. *)

(* (** XXX: We /NEED/ this line for [Equations Derive] to work, *)
(*  this flag is globally unset by std++, but Equations need obligations to be transparent. *) *)
(* Set Transparent Obligations. *)

(* Derive NoConfusion NoConfusionHom for list. *)

(* Definition scope := (list unit). *)

(* (** Variables in a context *) *)
(* Inductive var : scope → Type := *)
(* | Vz : forall {S : scope} {s}, var (s::S) *)
(* | Vs : forall {S : scope} {s}, var S -> var (s::S) *)
(* . *)
(* Derive Signature NoConfusion for var. *)

(* Inductive tyctx (ty : Type) : scope → Type := *)
(* | empC : tyctx ty [] *)
(* | consC : forall{Γ}, ty → tyctx ty Γ → tyctx ty (()::Γ) *)
(* . *)
(* Arguments empC {_}. *)
(* Arguments consC {_ _} _ _. *)

(* Equations list_of_tyctx {S ty} (Γ : tyctx ty S) : list ty := *)
(*   list_of_tyctx empC := []; *)
(*   list_of_tyctx (consC τ Γ') := τ::list_of_tyctx Γ'. *)

(* Equations tyctx_app {S1 S2 ty} (c1 : tyctx ty S1) (c2 : tyctx ty S2) : tyctx ty (S1++S2) := *)
(*   tyctx_app empC         c2 := c2; *)
(*   tyctx_app (consC τ c1) c2 := consC τ (tyctx_app c1 c2). *)

(* Inductive typed_var {ty : Type}: forall {S}, tyctx ty S → var S → ty → Prop := *)
(* | typed_var_Z S (τ : ty) (Γ : tyctx ty S) : *)
(*   typed_var (consC τ Γ) Vz τ *)
(* | typed_var_S S (τ τ' : ty) (Γ : tyctx ty S) v : *)
(*   typed_var Γ v τ → *)
(*   typed_var (consC τ' Γ) (Vs v) τ *)
(* . *)
