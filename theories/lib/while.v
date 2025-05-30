From gitrees Require Import prelude gitree.
Export IF_nat.

Section while.
  Context {E : opsInterp}.
  Context {R} `{!Cofe R}.
  Context `{!SubOfe unitO R}.
  Context `{!SubOfe natO R}.
  Notation IT := (IT E R).
  Notation ITV := (ITV E R).

  Program Definition pre_while (while : IT -n> IT -n> IT) : IT -n> IT -n> IT :=
    λne cond body, IF cond (SEQ body (Tick (while cond body))) (Ret ()).
  Solve All Obligations with solve_proper_please.

  #[local] Instance pre_while_contractive : Contractive pre_while.
  Proof. solve_contractive. Qed.
  Definition WHILE : IT -n> IT -n> IT := fixpoint pre_while.

  (** WHILE (α > 0) DO β *)
  Lemma WHILE_eq α β :
    WHILE α β ≡ IF α (SEQ β (Tick (WHILE α β))) (Ret ()).
  Proof.
    etrans.
    - apply (fixpoint_unfold pre_while _ _).
    - reflexivity.
  Qed.

End while.
