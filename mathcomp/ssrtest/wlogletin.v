(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect eqtype ssrbool.

Variable T : Type.
Variables P : T -> Prop.

Definition f := fun x y : T => x.

Lemma test1 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
wlog H : @fxy Pfxy / P x.
  match goal with |- (let fxy0 := f x y in P fxy0 -> P x -> P x) -> P x => by auto | _ => fail end.
exact: H.
Qed.

Lemma test2 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
wlog H : fxy Pfxy / P x.
  match goal with |- (forall fxy, P fxy -> P x -> P x) -> P x => by auto | _ => fail end.
exact: H.
Qed.

Lemma test3 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
move: {1}@fxy (Pfxy) (Pfxy).
match goal with |- (let fxy0 := f x y in P fxy0 -> P fxy -> P x) => by auto | _ => fail end.
Qed.

Lemma test4 : forall n m z: bool, n = z -> let x := n in x = m && n -> x = m && n.
move=> n m z E x H. 
case: true.   
  by rewrite  {1 2}E in (x) H |- *.
by rewrite {1}E in x H |- *.
Qed.
