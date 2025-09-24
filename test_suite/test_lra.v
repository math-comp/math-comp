From mathcomp Require Import all_boot ssralg ssrnum ssrint rat lra.

Local Open Scope ring_scope.

Lemma test (F : realFieldType) (x y : F) :
  x + 2 * y <= 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof. lra. Qed.

(* Print test. *)
(* Print Assumptions test.  (* Closed under the global context *) *)

Lemma test_rat (x y : rat) : x + 2 * y <= 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof. lra. Qed.

Lemma test_realDomain (R : realDomainType) (x y : R) :
  x + 2 * y <= 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof. lra. Qed.

Lemma test_realDomain' (R : realDomainType) (x : int) (y : R) :
  x%:~R + 2 * y <= 3 -> (2 * x)%:~R + y <= 3 -> x%:~R + y <= 2.
Proof. lra. Qed.

Section Tests.
Variable F : realFieldType.
Implicit Types x y : F.

Lemma test_cast : 0 <= 2 :> F.
Proof. lra. Qed.

Example test_div x y : x / 2 + y <= 3 -> x + y / 2 <= 3 -> x + y <= 4.
Proof. lra. Qed.

Example test_div_mul x : 1 / (2 * x) <= 1 / 2 / x + 1.
Proof. lra. Qed.

Example test_div_inv x : 1 / x^-1 <= x + 1.
Proof. lra. Qed.

Example test_div_opp x : (- x)^-1 <= - x^-1 + 1.
Proof. lra. Qed.

Example test_div_exp x : (x ^+ 2) ^-1 <= x ^-1 ^+ 2 + 1.
Proof. lra. Qed.

Lemma test_lt x y : x + 2 * y < 3 -> 2 * x + y <= 3 -> x + y < 2.
Proof. lra. Qed.

Lemma test_eq x y : x + 2 * y = 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof. lra. Qed.

Lemma test_eqop x y : x + 2 * y == 3 -> 2 * x + y <= 3 -> x + y <= 2.
Proof. lra. Qed.

Lemma test_prop_in_middle (C : Prop) x : x <= 2 -> C -> x <= 3.
Proof. lra. Qed.

Lemma test_opp x : x <= 2 -> -x >= -2.
Proof. lra. Qed.

Lemma test_iff x : x <= 2 <-> -x >= -2.
Proof. lra. Qed.

Lemma test_eq_bool x : x <= 2 = (-x >= -2).
Proof. lra. Qed.

Lemma test_not x : x <= 2 -> ~ (x > 2).
Proof. lra. Qed.

Lemma test_negb x : x <= 2 -> ~~ (x > 2).
Proof. lra. Qed.

Lemma test_and x : x <= 2 -> (x <= 3 /\ x <= 4).
Proof. lra. Qed.

Lemma test_andb x : x <= 2 -> (x <= 3) && (x <= 4).
Proof. lra. Qed.

Lemma test_or x : x <= 2 -> (x <= 3 \/ x <= 1).
Proof. lra. Qed.

Lemma test_orb x : x <= 2 -> (x <= 3) || (x <= 1).
Proof. lra. Qed.

Lemma test_exfalso x (xle2 : x <= 2) (xge3 : x >= 3) : bool.
Proof. lra. Qed.

Lemma test_rat_constant x : 0 <= x -> 1 / 3 * x <= 2^-1 * x.
Proof. lra. Qed.

Lemma test_rfstr (x : rat) : (x <= 2) || true = true.
Proof. lra. Qed.

End Tests.

(* Examples from the test suite of Coq *)
Section TestsCoq.
Variable F : realFieldType.
Implicit Types x y : F.

Lemma plus_minus x y : 0 = x + y -> 0 = x - y -> 0 = x /\ 0 = y.
Proof. lra. Qed.

Lemma plus_minus' x y : 0 = x + y -> 0 = x - y -> 0 = x /\ 0 = y.
Proof. move=> *; lra. Qed.

Lemma cst_test : 5^+5 = 5 * 5 * 5 * 5 * 5 :> F.
Proof. lra. Qed.

Goal forall x y, x <> x -> x > y.
Proof. move=> *; lra. Qed.

Lemma binomial x y : (x + y)^+2 = x^+2 + 2 * x * y + y^+2.
Proof. move=> *; lra. Qed.

Lemma hol_light19 x y : 2 * y + x = (x + y) + y.
Proof. lra. Qed.

Lemma vcgen_25 (n m jt j it i : F) :
  1 * it - 2 * i - 1 = 0 ->
  1 * jt - 2 * j - 1 = 0 ->
  1 * n - 10 = 0 ->
  0 <= -(4028%:R)  * i + 6222%:R * j + 705 * m + -(16674%:R) ->
  0 <= - 418 * i + 651 * j + 94 * m + -(1866%:R) ->
  0 <= - 209 * i + 302 * j + 47 * m - 839 ->
  0 <= - 1 * i + 1 * j - 1 ->
  0 <= - 1 * j + 1 * m + 0 ->
  0 <= 1 * j + 5 * m - 27 ->
  0 <= 2 * j - 1 * m + 2 ->
  0 <= 7 * j + 10 * m - 74 ->
  0 <= 18 * j - 139 * m + 1188%:R ->
  0 <= 1 * i + 0 ->
  0 <= 121 * i + 810 * j + -(7465%:R) * m + 64350%:R ->
  1 = - 2 * i + it.
Proof. move=> *; lra. Qed.

Lemma l1 x y z : `|x - z| <= `|x - y| + `|y - z|.
Proof.
Fail intros; split_Rabs; lra.  (* TODO should work *)
Abort.

Lemma l2 x y :
  x < `|y| -> y < 1 -> x >= 0 -> - y <= 1 -> `|x| <= 1.
Proof.
Fail intros; split_Rabs; lra.  (* TODO should work *)
Abort.

(*  Bug 5073 *)
Lemma opp_eq_0_iff x : -x = 0 <-> x = 0.
Proof. lra. Qed.

(* From L. Théry *)

Goal forall x y, x = 0 -> x * y = 0.
Proof. move=> *; nra. Qed.

Goal forall x y, 2 * x = 0 -> x * y = 0.
Proof. move=> *; nra. Qed.

Goal forall x y, - x * x >= 0 -> x * y = 0.
Proof. move=> *; nra. Qed.

Goal forall x, x * x >= 0.
Proof. move=> *; nra. Qed.

Goal forall x, -x^+2 >= 0 -> x - 1 >= 0 -> False.
Proof.
move=> *.
(* Requires CSDP *)
(* psatz 3. *)
(* Qed. *)
Abort.

Goal forall x, -x^+2 >= 0 -> x - 1 >= 0 -> False.
Proof. move=> *; nra. Qed.

Lemma motzkin' x y :
  (x^+2 + y^+2 + 1) * (x^+2 * y^+4 + x^+4*y^+2 + 1 - 3 * x^+2 * y^+2) >= 0.
Proof.
move=> *.
(* Requires CSDP *)
(* psatz 3. *)
(* Qed. *)
Abort.

Goal forall x, -x^+2 >= 0 -> x - 1 >= 0 -> False.
Proof. move=> *; nra. Qed.

Goal 1 / (1 - 1) = 0 :> F.
Proof.
Fail lra. (* division by zero *)
Abort.

Goal 0 / (1 - 1) = 0 :> F.
Proof. lra. Qed.  (* 0 * x = 0 *)

Goal 10 ^+ 2 = 100 :> F.
Proof. lra. Qed.  (* pow is reified as a constant *)

Goal ratr (1 / 2) = 1 / 2 :> F.
Proof. lra. Qed.

Goal 1 ^+ (2 + 2) = 1 :> F.
Proof. lra. Qed.

Goal 1 ^+ (2 + 2) = 1 :> F.
Proof. lra. Qed.

End TestsCoq.

Example test_abstract_rmorphism (R : realDomainType) (f : {rmorphism R -> R})
  (x y : R) : f y >= 0 -> f x + 2 * f (y + 1) <= f (3 * y + x) + 2.
Proof. lra. Qed.

Example test_concrete_rmorphism (R : realFieldType) (x y : rat) :
  ratr y >= 0 :> R -> ratr x + 2 * ratr (y + 1) <= ratr (3 * y + x) + 2 :> R.
Proof. lra. Qed.
