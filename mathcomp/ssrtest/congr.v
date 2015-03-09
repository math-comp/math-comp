(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool eqtype ssrnat.

Lemma test1 : forall a b : nat, a == b -> a == 0 -> b == 0.
Proof. move=> a b Eab Eac; congr (_ == 0) : Eac; exact: eqP Eab. Qed.

Definition arrow A B := A -> B.

Lemma test2 : forall a b : nat, a == b -> arrow (a == 0) (b == 0).
Proof. move=> a b Eab; congr (_ == 0); exact: eqP Eab. Qed.

Definition equals T (A B : T) := A = B.

Lemma test3 : forall a b : nat, a = b -> equals nat (a + b) (b + b).
Proof. move=> a b E; congr (_ + _); exact E. Qed.

Variable S : eqType.
Variable f : nat -> S.
Coercion f : nat >-> Equality.sort.

Lemma test4 : forall a b : nat, b = a -> @eq S (b + b) (a + a).
Proof. move=> a b Eba; congr (_ + _); exact:  Eba. Qed.

