(* TODO: remove this file when requiring Rocq >= 9.2
   and use the identical file in Corelib instead *)

From Corelib Require Export NatDef.

#[local] Set Implicit Arguments.

Module N.
Export N.
Definition to_nat (a : N) :=
  match a with
    | N0 => O
    | Npos p => Pos.to_nat p
  end.
End N.
