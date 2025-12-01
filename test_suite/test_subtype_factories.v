From HB Require Import structures.
From mathcomp Require Import all_boot ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Test0.

Variables (T : choiceType) (S : {pred T}).

Inductive B := mkB x & x \in S.
Definition vB u := let: mkB x _ := u in x.

HB.instance Definition _ := [isSub for vB].
HB.instance Definition _ := [Choice of B by <:].

End Test0.

Section Test1.

Variables (R : unitRingType) (S : divringClosed R).

HB.instance Definition _ := [SubChoice_isSubUnitRing of B S by <:].

End Test1.

Section Test2.

Variables (R : comUnitRingType) (A : unitAlgType R) (S : divalgClosed A).

HB.instance Definition _ := [SubNmodule_isSubLSemiModule of B S by <:].
HB.instance Definition _ := [SubRing_SubLmodule_isSubLalgebra of B S by <:].
HB.instance Definition _ := [SubLSemiAlgebra_isSubSemiAlgebra of B S by <:].

End Test2.

Section Test3.

Variables (F : fieldType) (S : divringClosed F).

HB.instance Definition _ := [SubSemiRing_isSubComSemiRing of B S by <:].
HB.instance Definition _ := [SubComUnitRing_isSubIntegralDomain of B S by <:].
HB.instance Definition _ := [SubIntegralDomain_isSubField of B S by <:].

End Test3.
