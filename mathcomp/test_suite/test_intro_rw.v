From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma test_dup1 : forall n : nat, odd n.
Proof. move=> /[dup] m n; suff: odd n by []. Abort.

Lemma test_dup2 : let n := 1 in False.
Proof. move=> /[dup] m n; have : m = n := erefl. Abort.

Lemma test_swap1 : forall (n : nat) (b : bool), odd n = b.
Proof. move=> /[swap] b n; suff: odd n = b by []. Abort.

Lemma test_swap1 : let n := 1 in let b := true in False.
Proof. move=> /[swap] b n; have : odd n = b := erefl. Abort.

Lemma test_apply A B : forall (f : A -> B) (a : A), False.
Proof.
move=> /[apply] b.
Check (b : B).
Abort.
