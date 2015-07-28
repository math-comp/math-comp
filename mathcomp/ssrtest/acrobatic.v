(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import ssreflect ssrbool eqtype ssrnat.

Lemma test1 : forall x y : nat, x = y -> forall z : nat, y == z -> x = z.
Proof.
by move=> x y + z /eqP <-; apply.
Qed.

Lemma test2 : forall (x y : nat) (e : x = y), e = e -> True.
Proof.
move=> + y + _ =>>  def_x.
Check (def_x : _ = y).
by [].
Qed.

Lemma test3 : forall x y : nat, x = y -> forall z : nat, y == z -> x = z.
Proof.
by move=>> -> /eqP.
Qed.