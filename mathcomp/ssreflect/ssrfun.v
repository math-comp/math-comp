From mathcomp Require Import ssreflect.
From Coq Require Export ssrfun.
From mathcomp Require Export ssrnotations.

Lemma Some_inj {T : nonPropType} : injective (@Some T).
Proof. by move=> x y []. Qed.

Notation void := Empty_set.

Definition of_void T (x : void) : T := match x with end.

Lemma of_voidK T : pcancel (of_void T) [fun _ => None].
Proof. by case. Qed.
