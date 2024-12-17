From mathcomp Require Import ssreflect mini_ssrfun mini_ssrbool.
From mathcomp Require Import mini_eqtype mini_ssrnat mini_seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

Notation "\sum_ ( m <= i < n ) F" := (sum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").

Lemma sum_geq m n F : n <= m -> \sum_(m <= i < n) F i = 0.
Proof. by rewrite /sum => /eqP->. Qed.

Lemma sum_recr m n F : m <= n ->
  \sum_(m <= i < n.+1) F i = \sum_(m <= i < n) F i + F n.
Proof.
move=> leq_mn; rewrite /sum subSn// -addn1 iota_add subnKC// foldr_cat/=.
by elim: iota (F n) => [|x s IHs] k; rewrite -?addnA -?IHs ?addn0.
Qed.

Lemma sum_recl m n F : m <= n ->
  \sum_(m <= i < n.+1) F i = F m + \sum_(m <= i < n) F (S i).
Proof.
move=> leq_mn; rewrite /sum subSn//=; congr (_ + _).
by move: (n - m) => k {leq_mn}; elim: k m => //= k IHk m; rewrite IHk.
Qed.

Lemma muln_sumr (m n k : nat) F :
  k * (\sum_(m <= i < n) F i) = \sum_(m <= i < n) k * F i.
Proof.
by rewrite /sum; elim: iota => [|x s IHs]; rewrite (muln0, mulnDr) ?IHs.
Qed.

Lemma eqn_sum (m n : nat) G F : (forall i, F i = G i) ->
  (\sum_(m <= i < n) F i) = \sum_(m <= i < n) G i.
Proof.
by rewrite /sum; elim: iota => [|x s IHs]//= eqFG; rewrite IHs ?eqFG.
Qed.
Arguments eqn_sum {m n} G F eq_FG.

Lemma muln_suml (m n k : nat) F :
  (\sum_(m <= i < n) F i) * k = \sum_(m <= i < n) F i * k.
Proof. by rewrite mulnC muln_sumr; apply: eqn_sum => i; rewrite mulnC. Qed.
