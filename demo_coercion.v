From mathcomp Require Import all_ssreflect ssralg ssrint.

Import GRing.Theory.

Local Open Scope ring_scope.

Section DemoCoercionsNatmul.

Variable R : ringType.

Variables (x : R) (n : nat).

Lemma test_nat : n + x + 1 = x + n.+1.
Proof.
rewrite -addn1.
(* now we need some printing of coercions *)
Enable Notation (all) : ring_coercions.
rewrite natrD.
Disable Notation (all) : ring_coercions.
by rewrite addrCA addrA.
Qed.

End DemoCoercionsNatmul.

Section DemoCoercionsIntmul.

Variable R : ringType.

Variables (x : R) (n : int).

Lemma test_int : n + x + 1 = x + (n + 1)%Z.
Proof.
(* now we need some printing of coercions *)
Enable Notation (all) : ring_coercions.
rewrite intrD.
Disable Notation (all) : ring_coercions.
by rewrite addrCA addrA.
Qed.

End DemoCoercionsIntmul.
