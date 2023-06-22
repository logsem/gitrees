From gitrees Require Import prelude gitree.

Section while.
  Context {E : opsInterp}.
  Notation IT := (IT E).
  Notation ITV := (ITV E).

  Program Definition pre_while (while : IT -n> IT -n> IT) : IT -n> IT -n> IT :=
    λne cond body, IF cond (SEQ body (Tick (while cond body))) (Nat 0).
  Solve All Obligations with solve_proper_please.

  #[local] Instance pre_while_contractive : Contractive pre_while.
  Proof. solve_contractive. Qed.
  Definition WHILE : IT -n> IT -n> IT := fixpoint pre_while.

  (** WHILE (α > 0) DO β *)
  Lemma WHILE_eq α β :
    WHILE α β ≡ IF α (SEQ β (Tick (WHILE α β))) (Nat 0).
  Proof. apply (fixpoint_unfold pre_while _ _). Qed.

End while.
