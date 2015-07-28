(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import ssreflect.

Ltac fancy H := case: H; last first.

Notation fancy := (tactic_view ltac:( fancy )).

Ltac replicate n what := do n! have:= what.

Notation replicate n := (tactic_view ltac:( replicate n )).

Lemma foo x (w : nat) (J : bool -> nat -> nat) : exists y, x=0+y.
Proof.
move/(replicate 6): (w) => w1 w2 w3 w4 w5 w6.
move/J/fancy: w => [w'||]; last exact: false.
  move: w' => /J/fancy[w''||]; last exact: false.
    by exists x.
  by exists x.
by exists x.
Qed.

Ltac unfld what top := rewrite /what; move: top.

Notation "% n" := (tactic_view ltac:( unfld n )) (at level 0).


Definition def := 4.

Lemma test : True -> def = 4.
Proof.
move=> /(% def) _.
match goal with |- 4 = 4 => reflexivity end.
Qed.
