(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrnat eqtype seq fintype zmodp.

Axiom P : forall T, seq T -> Prop.

Goal (forall T (s : seq T), P _ s).
move=> T s.
elim: s => [| x /lastP [| s] IH].
Admitted.

Goal forall x : 'I_1, x = 0 :> nat.
move=> /ord1 -> /=; exact: refl_equal.
Qed.

Goal forall x : 'I_1, x = 0 :> nat.
move=> x.
move=> /ord1 -> in x |- *.
exact: refl_equal.
Qed.
