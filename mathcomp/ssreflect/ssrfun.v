From mathcomp Require Import ssreflect.
From Coq Require Export ssrfun.
From mathcomp Require Export ssrnotations.

(******************************************************************************)
(* Local additions:                                                           *)
(*        void == a notation for the Empty_set type of the standard library.  *)
(*   of_void T == the canonical injection void -> T.                          *)
(******************************************************************************)

Lemma Some_inj {T : nonPropType} : injective (@Some T).
Proof. by move=> x y []. Qed.

Notation void := Empty_set.

Definition of_void T (x : void) : T := match x with end.

Lemma of_voidK T : pcancel (of_void T) [fun _ => None].
Proof. by case. Qed.

Lemma inj_compr A B C (f : B -> A) (h : C -> B) :
   injective (f \o h) -> injective h.
Proof. by move=> fh_inj x y /(congr1 f) /fh_inj. Qed.
