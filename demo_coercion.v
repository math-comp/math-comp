From mathcomp Require Import all_ssreflect ssralg.

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
