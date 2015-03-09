Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
move=> n m p Hmn Hnp; rewrite -ltnS.
Fail rewrite (_ : forall n0 m0 p0 : nat, m0 <= n0 -> n0 < p0 -> m0 < p0).
Fail rewrite leq_ltn_trans.
Admitted.