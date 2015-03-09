Require Import ssreflect.
Ltac mycut x :=
  let tx := type of x in
  cut tx.

Lemma test : True.
Proof.
by mycut I=> [ x | ]; [ exact x | exact I ].
Qed.