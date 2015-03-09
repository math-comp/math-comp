Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.


Lemma test1 n : n >= 0.
Proof.
have [:s1] @h m : 'I_(n+m).+1.
  apply: Sub 0 _.
  abstract: s1 m.
  by auto. 
cut (forall m, 0 < (n+m).+1); last assumption.
rewrite [_ 1 _]/= in s1 h *.
by [].
Qed.

Lemma test2 n : n >= 0.
Proof.
have [:s1] @h m : 'I_(n+m).+1 := Sub 0 (s1 m).
  move=> m; reflexivity.
cut (forall m, 0 < (n+m).+1); last assumption.
by [].
Qed.

Lemma test3 n : n >= 0.
Proof.
Fail have [:s1] @h m : 'I_(n+m).+1 by apply: (Sub 0 (s1 m)); auto.
have [:s1] @h m : 'I_(n+m).+1 by apply: (Sub 0); abstract: s1 m; auto.
cut (forall m, 0 < (n+m).+1); last assumption.
by [].
Qed.

Lemma test4 n : n >= 0.
Proof.
have @h m : 'I_(n+m).+1 by apply: (Sub 0); abstract auto.
by [].
Qed.


