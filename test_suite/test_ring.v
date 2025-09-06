From mathcomp Require Import all_boot ssralg ssrnum ssrint rat.
From mathcomp Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Goal forall a b : nat, (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2%N * a * b.
Proof. move=> a b; ring. Qed.

Goal forall a b : int, (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2 * a * b.
Proof. move=> a b; ring. Qed.

Goal forall a b : rat, (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2%:R * a * b.
Proof. move=> a b; ring. Qed.

Goal forall a b : int * rat, (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 2%:R * a * b.
Proof. move=> a b; ring. Qed.

Section AbstractCommutativeRing.

Variables (R : comRingType) (a b c : R) (n : nat).

(* Examples from the Coq Reference Manual, but for an instance of MathComp's
   (abstract) commutative ring. *)

(* Using the _%:R embedding from nat to R (2%R is read as 2%N%:R) *)
Goal (a + b + c) ^+ 2 =
     a * a + b ^+ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
Proof. ring. Qed.

Goal (a + b + c) ^+ 2 =
     a * a + b ^+ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
Proof. (#[verbose] ring). Qed.

(* Using the _%:~R embedding from int to R (2 is coerced to (Posz 2) : int) *)
Goal (a + b + c) ^+ 2 =
     a * a + b ^+ 2 + c * c + 2%:~R * a * b + 2%:~R * a * c + 2%:~R * b * c.
Proof. ring. Qed.

(* With an identity hypothesis *)
(* Using the _%:R embedding from nat to R *)
Goal 2 * a * b = 30 -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30.
Proof. move=> H; ring: H. Qed.

(* With an identity hypothesis *)
(* Using the _%:~R embedding from int to R *)
Goal 2%:~R * a * b = 30%:~R -> (a + b) ^+ 2 = a ^+ 2 + b ^+ 2 + 30%:~R.
Proof. move=> H; ring: H. Qed.

Goal (n.+1)%:R = n%:R + 1 :> R.
Proof. ring. Qed.

Goal a * 2 = 2 * a.
Proof. ring. Qed.

End AbstractCommutativeRing.

Section AbstractRingMorphism.

Variables (R : ringType) (S : comRingType) (f : {rmorphism R -> S}) (a b : R).

Goal f ((a + b) ^+ 2) = f a ^+ 2 + f b ^+ 2 + 2 * f a * f b.
Proof. ring. Qed.

End AbstractRingMorphism.

Section AbstractAdditiveFunction.

Variables (U V : zmodType) (R : comRingType).
Variables (g : {additive U -> V}) (f : {additive V -> R}) (a : U) (b : V).

Goal f (g a + b) ^+ 2 = f (g a) ^+ 2 + f b ^+ 2 + f (g (a *+ 2)) * f b.
Proof. ring. Qed.

End AbstractAdditiveFunction.

Section NumeralExamples.

Variable (R : comRingType).

(* With numeral constants *)
Goal 20 * 3 = 60 :> R.
Proof. ring. Qed.

Goal 20%:~R * 3%:~R = 60%:~R :> R.
Proof. ring. Qed.

Goal 200%:~R * 30%:~R = 6000%:~R :> R.
Proof. ring. Qed.

Goal 2%:~R * 10%:~R ^+ 2 * 3%:~R * 10%:~R ^+ 2 = 6%:~R * 10%:~R ^+ 4 :> R.
Proof. ring. Qed.

Goal 200 * 30 = 6000%:R :> R.
Proof. ring. Qed.

Goal 200 * 30 = 6000%:R :> int.
Proof. ring. Qed.

Goal 20 * 3 = 60 :> rat.
Proof. ring. Qed.

Goal 200 * 30 = 6000%:R :> rat.
Proof. ring. Qed.

End NumeralExamples.

Section MoreVariables.

Variables (q w e r t y u i o p a s d f g h j k l : int).

Lemma test_vars :
  q * w * e * r * t * y * u * i * o * p * a * s * d * f * g * h * j * k * l =
  l * w * e * r * t * y * u * i * o * p * a * s * d * f * g * h * j * k * q.
Proof. ring. Qed.

End MoreVariables.
