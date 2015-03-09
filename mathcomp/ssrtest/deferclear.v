(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool eqtype fintype ssrnat.

Variable T : Type.

Lemma test0 : forall a b c d : T, True.
Proof. by move=> a b {a} a c; exact I. Qed.

Variable P : T -> Prop.

Lemma test1 : forall a b c : T, P a -> forall d : T, True.
Proof. move=> a b {a} a _ d; exact I. Qed.

Definition Q := forall x y : nat, x = y.
Axiom L : 0 = 0 -> Q.
Axiom L' : 0 = 0 -> forall x y : nat, x = y.
Lemma test3 : Q.
by apply/L.
Undo.
rewrite /Q.
by apply/L.
Undo 2.
by apply/L'.
Qed.

