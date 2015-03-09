Require Import ssreflect ssrbool.

Lemma v : True -> bool -> bool. Proof. by []. Qed.

Reserved Notation " a -/ b " (at level 0).
Reserved Notation " a -// b " (at level 0).
Reserved Notation " a -/= b " (at level 0).
Reserved Notation " a -//= b " (at level 0).

Lemma test : forall a b c, a || b || c.
Proof.
move=> ---a--- - -/=- -//- -/=- -//=- b [|-].
move: {-}a => /v/v-H; have _ := H I I.
Fail move: {-}a {H} => /v-/v-H.
have - -> : a = (id a) by [].
have --> : a = (id a) by [].
have - - _ : a = (id a) by [].
have -{1}-> : a = (id a) by [].
  by admit.
move: a.
case: b => -[] //.
by admit.
Qed.
