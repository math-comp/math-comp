From mathcomp Require Import all_ssreflect ssralg.

Import GRing.Theory.

Local Open Scope ring_scope.

Arguments GRing.add : > <.

Section DemoCoercionsNatmul.

Variable R : ringType.

Variables (x : R) (n : nat).

Lemma test_nat : n + x + 1 = x + n.+1.
Proof.
(* n + x + 1 = x + n.+1 *)
rewrite -addn1.
(* n + x + 1 = x + (n + 1)%:R *)
rewrite natrD.
(* n + x + 1 = x + (n + 1) *)
by rewrite addrCA addrA.
Qed.

(* but %:R needs to be printed on LHS of equalities *)
Check n%:R = x.
Check n%:R <> x.
Check n%:R == x.
Check n%:R != x.

End DemoCoercionsNatmul.
