(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import ssreflect.

Set Implicit Arguments.

Axiom P : nat -> nat -> Prop.

Axiom tr :
  forall x y z, P x y -> P y z -> P x z.

Lemma test a b c : P a c -> P a b.
Proof.
intro H.
Fail have [: s1 s2] H1 : P a b := @tr _ _ _ s1 s2.
have [: w s1 s2] H1 : P a b := @tr _ w _ s1 s2.
Abort.

