Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool eqtype ssrnat.
Axiom daemon : False. Ltac myadmit := case: daemon.

Lemma test x : (x == x) = (x + x.+1 == 2 * x + 1).
case: (X in _ = X) / eqP => _.
match goal with |- (x == x) = true => myadmit end.
match goal with |- (x == x) = false => myadmit end.
Qed.

Lemma test1 x : (x == x) = (x + x.+1 == 2 * x + 1).
elim: (x in RHS).
match goal with |- (x == x) = _ => myadmit end.
match goal with |- forall n, (x == x) = _ -> (x == x) = _ => myadmit end.
Qed.

