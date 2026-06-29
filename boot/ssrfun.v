From mathcomp Require Import ssreflect.
From Corelib Require Export ssrfun.
From mathcomp Require Export ssrnotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**********************)
(* not yet backported *)
(**********************)

Lemma taggedK {I : Type} (T_ : I -> Type) (s : {i : I & T_ i}) :
  Tagged T_ (tagged s) = s.
Proof. by case: s. Qed.

Definition swap_pair {T1 T2 : Type} (x : T1 * T2) := (x.2, x.1).

(* Note that this lemma coudn't be an instance of the [involutive] predicate. *)
Lemma swap_pairK {T1 T2 : Type} : @cancel _ (T1 * T2) swap_pair swap_pair.
Proof. by case. Qed.
