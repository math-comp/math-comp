Require Import ssreflect.

Axiom oops : 3=4.

Ltac ssrdone33 := exact: oops.

Lemma false : 5 = 6.
Proof.
congr (S (S _)).
Fail done.
move => /33/.
Qed.

Lemma false2 : 3 = 4 /\ 2 + 3 = 5.
Proof.
split => /33/=.
lazymatch goal with
| |- 2 + 3 = 5 => fail
| |- 5 = 5 => done
end.
Qed.

Lemma test5 : 1=1 /\ 2=2.
Proof.
move=> /0/.
split=> /0/.
Qed.
