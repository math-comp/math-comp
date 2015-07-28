(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import eqtype ssrnat.

Lemma test1 : forall n m : nat, n = m -> m * m + n * n = n * n + n * n.
move=> n m E; have [{2}-> _] : n * n = m * n /\ True by move: E => {1}<-.
by move: E => {3}->.
Qed.

Lemma test2 : forall n m : nat, True /\ (n = m -> n * n = n * m).
by move=> n m; constructor=> [|{2}->].
Qed.

