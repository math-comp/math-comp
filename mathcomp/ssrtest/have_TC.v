Require Import ssreflect.

Class foo (T : Type) := { n : nat }.
Instance five : foo nat := {| n := 5 |}.

Definition bar T {f : foo T} m : Prop :=
  @n _ f = m.

Eval compute in (bar nat 7).

Lemma a : True.
set toto := bar _ 8.
have titi : bar _ 5.
  reflexivity.
have titi2 : bar _ 5 := .
  Fail reflexivity.
  by admit.
have totoc (H : bar _ 5) : 3 = 3 := eq_refl.
move/totoc: nat => _.
exact I.
Qed.

Set SsrHave NoTCResolution.

Lemma a' : True.
set toto := bar _ 8.
have titi : bar _ 5.
  Fail reflexivity.
  by admit.
have titi2 : bar _ 5 := .
  Fail reflexivity.
  by admit.
have totoc (H : bar _ 5) : 3 = 3 := eq_refl.
move/totoc: nat => _.
exact I.
Qed.
