Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrnat.

Goal (forall x y : nat, True).
move=> x y.
wlog suff: x y / x <= y.
Admitted.
