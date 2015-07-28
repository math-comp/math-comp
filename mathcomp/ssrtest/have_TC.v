(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.

Axiom daemon : False. Ltac myadmit := case: daemon.

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
  by myadmit.
have totoc (H : bar _ 5) : 3 = 3 := eq_refl.
move/totoc: nat => _.
exact I.
Qed.

Set SsrHave NoTCResolution.

Lemma a' : True.
set toto := bar _ 8.
have titi : bar _ 5.
  Fail reflexivity.
  by myadmit.
have titi2 : bar _ 5 := .
  Fail reflexivity.
  by myadmit.
have totoc (H : bar _ 5) : 3 = 3 := eq_refl.
move/totoc: nat => _.
exact I.
Qed.
