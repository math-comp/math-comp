Require Import ssreflect ssrbool ssrnat.

Definition addnAC := (addnA, addnC).

Lemma test x y z : x + y + z =  x + y.

ssrinstancesoftpat (_ + _).
ssrinstancesofruleL2R addnC.
ssrinstancesofruleR2L addnA.
ssrinstancesofruleR2L addnAC.
Fail ssrinstancesoftpat (_ + _ in RHS). (* Not implemented *)
Admitted.