(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool.
Axiom daemon : False. Ltac myadmit := case: daemon.

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
  by myadmit.
move: a.
case: b => -[] //.
by myadmit.
Qed.
