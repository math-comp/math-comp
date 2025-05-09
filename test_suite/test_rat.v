From mathcomp Require Import all_boot all_order all_algebra.

Local Open Scope ring_scope.

Goal 2%:Q + 2%:Q = 4%:Q.
Proof. reflexivity. Qed.

Goal - 2%:Q = -1 * 2%:Q.
Proof. reflexivity. Qed.

Goal 2%:Q ^+ 2 = 4%:Q.
Proof. reflexivity. Qed.

Goal (-1)^-1 = -1 :> rat.
Proof. reflexivity. Qed.

Local Open Scope rat_scope.

Check 12.
Check 3.14.
Check -3.14.
Check 0.5.
Check 0.2.
