From stdpp Require Export pretty.

From gitrees.examples.heap_lang Require Import lang.
From iris.prelude Require Import options.

(** * Pretty printing for HeapLang values *)

Global Instance pretty_loc : Pretty loc :=
  λ l, pretty l.(loc_car).

Global Instance pretty_base_lit : Pretty base_lit :=
  λ l, match l with
       | LitInt z => pretty z
       | LitBool b => if b then "true" else "false"
       | LitUnit => "()"
       | LitLoc l => "(loc " +:+ pretty l +:+ ")"
       end.

Global Instance pretty_binder : Pretty binder :=
  λ b, match b with
       | BNamed x => x
       | BAnon => "<>"
       end.

(** Note that this instance does not print function bodies and is thus not
injective (unlike most `pretty` instances). *)
Global Instance pretty_val : Pretty val :=
  fix go v :=
    match v with
    | LitV l => "#" +:+ pretty l
    | RecV f x e =>
      match f with
      | BNamed f => "rec: " +:+ f +:+ " " +:+ pretty x +:+ " := <body>"
      | BAnon => "λ: " +:+ pretty x +:+ ", <body>"
      end
    | PairV v1 v2 => "(" +:+ go v1 +:+ ", " +:+ go v2 +:+ ")"
    | InjLV v => "inl (" +:+ go v +:+ ")"
    | InjRV v => "inr (" +:+ go v +:+ ")"
    end.

Global Instance pretty_un_op : Pretty un_op :=
  λ op, match op with
        | NegOp => "~"
        | MinusUnOp => "-"
        end.

Global Instance pretty_bin_op : Pretty bin_op :=
  λ op, match op with
        | PlusOp => "+"
        | MinusOp => "-"
        | MultOp => "*"
        | QuotOp => "`quot`"
        | RemOp => "`rem`"
        | AndOp => "&"
        | OrOp => "|"
        | XorOp => "`xor`"
        | ShiftLOp => "<<"
        | ShiftROp => ">>"
        | LeOp => "≤"
        | LtOp => "<"
        | EqOp => "="
        | OffsetOp => "+ₗ"
        end.
