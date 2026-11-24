From mathcomp Require Import boot order algebra.

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

(* Long literal: previously overflowed the stack via the unary-nat parser. *)
Check 3.141592653589793238462643383279.

(* Zero with a fractional part: printer collapses to "0". *)
Check 0.0.

Local Close Scope rat_scope.

(* Ring-scope cast notation: %:RR lifts a rat literal into any unitRingType. *)
Lemma test_RR_cast (R : unitRingType) : (3.14%:RR : R) = ratr 3.14%Q.
Proof. by []. Qed.
