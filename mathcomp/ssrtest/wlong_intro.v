Require Import ssreflect ssrbool ssrnat.

Goal (forall x y : nat, True).
move=> x y.
wlog suff: x y / x <= y.
Admitted.
