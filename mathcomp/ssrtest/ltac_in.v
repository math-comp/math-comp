Require Import ssreflect ssrbool eqtype ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* error 1 *)

Ltac subst1 H := move: H ; rewrite {1} addnC; move => H.
Ltac subst2 H := rewrite addnC in H.

Goal ( forall a b: nat, b+a = 0 -> b+a=0).
Proof. move => a b hyp. subst1 hyp. subst2 hyp. done. Qed.

